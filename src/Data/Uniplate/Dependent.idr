||| A dependent version of `Data.Uniplate`
||| Types can be quite complex, so I suggest starting with `Data.Uniplate`
module Data.Uniplate.Dependent

import Data.DPair
import Data.List.Quantifiers

import public Data.Uniplate

public export
data DRepr : Type -> Type where
    DRZero : DRepr idx
    DROne : idx -> DRepr idx
    DRTwo : DRepr idx -> DRepr idx -> DRepr idx

public export
data DChildren : DRepr idx -> (idx -> Type) -> Type where
    DZero : DChildren DRZero f
    DOne : forall i. f i -> DChildren (DROne i) f
    DTwo : DChildren l f -> DChildren r f -> DChildren (DRTwo l r) f

public export
dmap : (forall i. f i -> g i) -> DChildren repr f -> DChildren repr g
dmap f DZero = DZero
dmap f (DOne x) = DOne (f x)
dmap f (DTwo x y) = DTwo (dmap f x) (dmap f y)

public export
dtraverse : Applicative m => (forall i. f i -> m (g i)) -> DChildren repr f -> m (DChildren repr g)
dtraverse f DZero = pure DZero
dtraverse f (DOne x) = DOne <$> f x
dtraverse f (DTwo x y) = DTwo <$> dtraverse f x <*> dtraverse f y

public export
toListExists : DChildren repr f -> List (Exists f)
toListExists cs = toListExistsOnto cs []
  where
    toListExistsOnto : forall repr. DChildren repr f -> List (Exists f) -> List (Exists f)
    toListExistsOnto DZero acc = acc
    toListExistsOnto (DOne x) acc = Evidence _ x :: acc
    toListExistsOnto (DTwo x y) acc = toListExistsOnto x $ toListExistsOnto y acc

public export
dFoldMap : Monoid m => (forall i. f i -> m) -> DChildren repr f -> m
dFoldMap g DZero = neutral
dFoldMap g (DOne x) = g x
dFoldMap g (DTwo x y) = dFoldMap g x <+> dFoldMap g y

public export
record DPlate {0 idx : Type} (repr : DRepr idx) (from : Type) (to : idx -> Type) where
    constructor MkDPlate
    cs : DChildren repr to
    gen : DChildren repr to -> from

public export
interface DUniplate (0 idx : Type) (0 f : idx -> Type) | f where
    0 DGetRepr : (0 i : _) -> f i -> DRepr idx
    duniplate : forall i. (x : f i) -> DPlate (DGetRepr i x) (f i) f

    ddescend : forall i. (forall i. f i -> f i) -> f i -> f i
    ddescend op x =
        let MkDPlate cs gen = duniplate x
         in gen (dmap op cs)

    ddescendM : forall i. Applicative m => (forall i. f i -> m (f i)) -> f i -> m (f i)
    ddescendM op x =
        let MkDPlate cs gen = duniplate x
         in gen <$> dtraverse op cs

public export
interface DBiplate (0 idx : _) (0 from : Type) (0 to : idx -> Type) | from, to where
    0 DBiGetRepr : from -> DRepr idx
    dbiplate : (x : from) -> DPlate (DBiGetRepr x) from to

    biddescend : (forall i. to i -> to i) -> from -> from
    biddescend op x =
        let MkDPlate cs gen = dbiplate {to} x
         in gen (dmap op cs)

    biddescendM : Applicative m => (forall i. to i -> m (to i)) -> from -> m from
    biddescendM op x =
        let MkDPlate cs gen = dbiplate {to} x
         in gen <$> dtraverse op cs

||| Get the direct children of a node
public export
children : DUniplate idx f => f i -> List (Exists f)
children x = toListExists $ cs $ duniplate x

||| Start a new plate, not containing the target
public export
dplate : forall from. from -> DPlate DRZero from to
dplate x = MkDPlate DZero (\DZero => x)

||| The value to the right is the target
public export
(|*) : forall i. DPlate l (to i -> from) to -> to i -> DPlate (DRTwo l (DROne i)) from to
MkDPlate cs gen |* x = MkDPlate (DTwo cs (DOne x)) (\(DTwo cs (DOne x)) => gen cs x)

||| The value to the right contains the target
||| Note: due to https://github.com/idris-lang/Idris2/issues/2737,
||| you may need to use `assert_total`.
public export
(|+) :
    forall i.
    DBiplate idx item to =>
    DPlate l (item -> from) to ->
    (x : item) ->
    DPlate (DRTwo l (DBiGetRepr {to} x)) from to
MkDPlate ls lgen |+ x =
    let MkDPlate rs rgen = dbiplate x
     in MkDPlate (DTwo ls rs) (\(DTwo lr rs) => lgen ls (rgen rs))

||| The value to the right does not contain the target
public export
(|-) : forall i. DPlate repr (item -> from) to -> item -> DPlate repr from to
MkDPlate cs gen |- x = MkDPlate cs (\cs => gen cs x)

||| Fused form of `plate f |* x`
||| This replaces an `RTwo RZero ROne` with `ROne`
public export
dplateStar : forall i. (to i -> from) -> to i -> DPlate (DROne i) from to
dplateStar f x = MkDPlate (DOne x) (\(DOne x) => f x)

||| Fused form of `plate f |+ x`
||| This replaces an `RTwo RZero ROne` with `ROne`
||| Note: due to https://github.com/idris-lang/Idris2/issues/2737,
||| you may need to use `assert_total`.
public export %tcinline
dplatePlus : DBiplate idx item to => (item -> from) -> (x : item) -> DPlate (DBiGetRepr {to} x) from to
dplatePlus f x =
    let MkDPlate cs gen = dbiplate x
     in MkDPlate cs (\cs => f (gen cs))

||| Get all children of a node, including the node itself
||| and non-direct descendents.
public export
duniverse : DUniplate idx f => f i -> List (Exists f)
duniverse x = Evidence _ x :: assert_total (dFoldMap duniverse (duniplate x).cs)

-- Instances

{- TODO: fix this

public export
[Id] DUniplate idx f where
    DGetRepr i x = DOne i
    duniplate x = ?dash

public export
DUniplate (List idx) (All f) where
    DGetRepr [] [] = DRZero
    DGetRepr (_ :: i) (_ :: _) = DROne i

    duniplate [] = dplate []
    duniplate (x :: xs) = dplateStar (x ::) xs

public export
{0 i : List idx} -> {f : idx -> Type} -> DBiplate idx (All f i) f where
    DBiGetRepr i xs = ?tjasdhj

    dbiplate xs = ?hjadgh
