module Data.Uniplate

import Data.Vect
import Data.List1

%default total

infixl 3 |*
infixl 3 |+
infixl 3 ||+
infixl 3 |-

||| How the children of a given node are represented
public export
data Repr : Type where
    RZero : Repr
    ROne : Repr
    RTwo : Repr -> Repr -> Repr

%name Repr repr

||| The children of a node
public export
data Children : Repr -> Type -> Type where
    Zero : Children RZero a
    One : a -> Children ROne a
    Two : Children l a -> Children r a -> Children (RTwo l r) a

public export
Functor (Children repr) where
    map f Zero = Zero
    map f (One x) = One (f x)
    map f (Two x y) = Two (map f x) (map f y)

public export
Foldable (Children repr) where
    foldr f z Zero = z
    foldr f z (One x) = f x z
    foldr f z (Two x y) = foldr f (foldr f z y) x

    foldl f z Zero = z
    foldl f z (One x) = f z x
    foldl f z (Two x y) = foldl f (foldl f z x) y

    null Zero = True
    null _ = False

    foldlM f z Zero = pure z
    foldlM f z (One x) = f z x
    foldlM f z (Two x y) = foldlM f z x >>= (\z => foldlM f z y)

    toList cs = toListOnto cs []
      where
        toListOnto : forall repr. Children repr ty -> List ty -> List ty
        toListOnto Zero acc = acc
        toListOnto (One x) acc = x :: acc
        toListOnto (Two x y) acc = toListOnto x $ toListOnto y acc

    foldMap f Zero = neutral
    foldMap f (One x) = f x
    foldMap f (Two x y) = foldMap f x <+> foldMap f y

public export
Traversable (Children repr) where
    traverse f Zero = pure Zero
    traverse f (One x) = One <$> f x
    traverse f (Two x y) = Two <$> traverse f x <*> traverse f y

public export
record Plate (from : Type) (to : Type) where
    constructor MkPlate
    {0 repr : Repr}
    cs : Children repr to
    gen : Children repr to -> from

public export
interface Uniplate ty where
    ||| Get the direct children of a node
    ||| and a way to rebuild that node with modified children
    uniplate : (x : ty) -> Plate ty ty

    descend : (ty -> ty) -> ty -> ty
    descend f x =
        let MkPlate cs gen = uniplate x
         in gen (map f cs)

    descendM : Applicative m => (ty -> m ty) -> ty -> m ty
    descendM f x =
        let MkPlate cs gen = uniplate x
         in gen <$> traverse f cs

public export
interface Uniplate to => Biplate from to where
    biplate : (x : from) -> Plate from to

    bidescend : (to -> to) -> from -> from
    bidescend f x =
        let MkPlate cs gen = biplate x
         in gen (map f cs)

    bidescendM : Applicative m => (to -> m to) -> from -> m from
    bidescendM f x =
        let MkPlate cs gen = biplate x
         in gen <$> traverse f cs

compose : Biplate t a => Children r t -> Plate (Children r t) a
compose Zero = MkPlate Zero (\Zero => Zero)
compose (One x) =
    let MkPlate cs gen = biplate x
     in MkPlate cs (\cs => One (gen cs))
compose (Two x y) =
    let MkPlate xs genx = compose x
        MkPlate ys geny = compose y
     in MkPlate (Two xs ys) (\(Two xs ys) => Two (genx xs) (geny ys))

public export
[Compose] Biplate outer inner => Biplate inner to => Biplate outer to where
    biplate x =
        let MkPlate os geno = biplate {to = inner} x
            MkPlate is geni = compose os
         in MkPlate is (\is => geno (geni is))

    bidescend f x =
        let MkPlate cs gen = biplate @{Compose {outer, inner, to}} x
         in gen (f <$> cs)
    bidescendM f x =
        let MkPlate cs gen = biplate @{Compose {outer, inner, to}} x
         in gen <$> traverse f cs

public export
children : Uniplate ty => ty -> List ty
children x = toList $ cs $ uniplate x

||| Start a new plate, not containing the target
public export
plate : from -> Plate from to
plate x = MkPlate { cs = Zero, gen = \Zero => x}

||| The value to the right is the target
public export
(|*) : Plate (to -> from) to -> to -> Plate from to
MkPlate cs gen |* x = MkPlate (Two cs (One x)) (\(Two cs (One x)) => gen cs x)

||| The value to the right contains the target
||| Note: due to https://github.com/idris-lang/Idris2/issues/2737,
||| you may need to use `assert_total`.
public export %tcinline
(|+) :
    Biplate item to =>
    Plate (item -> from) to ->
    item ->
    Plate from to
MkPlate ls lgen |+ x =
    let MkPlate rs rgen = biplate x
     in MkPlate (Two ls rs) (\(Two ls rs) => lgen ls (rgen rs))

||| The value to the right contains the target 2 'layers' down
||| This is equivalent to `|+` using the `Compose` implementation of `Biplate`
public export %tcinline
(||+) :
    Biplate outer inner =>
    Biplate inner to =>
    Plate (outer -> from) to ->
    outer ->
    Plate from to
p ||+ x = (|+) @{Compose {outer, inner, to}} p x

||| The value to the right does not contain the target
public export
(|-) : Plate (item -> from) to -> item -> Plate from to
MkPlate cs gen |- x = MkPlate cs (\cs => gen cs x)

||| Fused form of `plate f |* x`
||| This replaces an `RTwo RZero ROne` with `ROne`
public export
plateStar : (to -> from) -> to -> Plate from to
plateStar f x = MkPlate (One x) (\(One x) => f x)

||| Fused form of `plate f |+ x`
||| Note: due to https://github.com/idris-lang/Idris2/issues/2737,
||| you may need to use `assert_total`.
public export %tcinline
platePlus : Biplate item to => (item -> from) -> (x : item) -> Plate from to
platePlus f x =
    let MkPlate cs gen = biplate x
     in MkPlate cs (\cs => f (gen cs))

||| Create a plate by providing a mapping to or from another type
||| i.e. a profunctor on `Plate`
public export
plateVia : Biplate s to => (f : s -> t) -> (g : t -> s) -> t -> Plate t to
plateVia f g x =
    let MkPlate cs gen = biplate $ g x
     in MkPlate cs (\cs => f (gen cs))

||| Get all children of a node, including the node itself
||| and non-direct descendents.
public export
universe : Uniplate ty => ty -> List ty
universe x = x :: assert_total (foldMap universe (uniplate x).cs)

||| Apply a function to each sub-node, then to the node itself
public export
transform : Uniplate ty => (ty -> ty) -> ty -> ty
transform f = f . assert_total (descend (transform f))

||| Apply a monadic function to each sub-node, then to the node itself
public export
transformM : Uniplate ty => Monad m => (ty -> m ty) -> ty -> m ty
transformM f = assert_total (descendM (transformM f)) >=> f

||| Find the fixed point of a function applied to every sub-node of a node
||| This ensures there is nowhere in the node that can have the function applied
||| ie forall f, x. all (isNothing . f) (universe (fixpoint f x)) = True
|||
||| You can use `fixAdd` to combine 2 functions
||| Note: it is up to the user to confirm that this is total
||| Especially when using `fixAdd`, as there may be subtle conflicts between operations
public export covering %inline
fixpoint : Uniplate ty => (ty -> Maybe ty) -> ty -> ty
fixpoint f = transform fix
  where
    fix : ty -> ty
    fix x = maybe x (fixpoint f) (f x)

||| Combine 2 functions that return `Maybe`
||| prefering the first one, if both would return `Just`
public export
fixAdd : (a -> Maybe b) -> (a -> Maybe b) -> (a -> Maybe b)
fixAdd f g x = f x <|> g x

||| Perform a fold on a node and it's sub-nodes
||| This is a paramorphism
public export
para : Uniplate ty => (ty -> List r -> r) -> ty -> r
para f x = f x $ assert_total $ map (para f) $ children x

-- Instances

public export
[Id] Uniplate a where
    uniplate x = plateStar id x

public export
[FromUni] Uniplate a => Biplate a a where
    biplate = uniplate

public export
Uniplate (List a) where
    uniplate [] = plate []
    uniplate (x :: xs) = plateStar (x ::) xs

public export
Biplate (List a) a using Id where
    biplate [] = plate []
    biplate (x :: xs) = assert_total $ plateStar (::) x |+ xs

public export
Biplate (Maybe a) a using Id where
    biplate Nothing = plate Nothing
    biplate (Just x) = plateStar Just x

public export
Uniplate (SnocList a) where
    uniplate [<] = plate [<]
    uniplate (xs :< x) = plateStar (:< x) xs

public export
Biplate (SnocList a) a using Id where
    biplate [<] = plate [<]
    biplate (xs :< x) = assert_total $ platePlus (:<) xs |* x

public export
Biplate (Vect len a) a using Id where
    biplate [] = plate []
    biplate (x :: xs) = plateStar (::) x |+ xs 

public export
Biplate (List1 a) a using Id where
    biplate (x ::: xs) = plateStar (:::) x |+ xs

public export
Biplate String Char using Id where
    biplate str = plateVia pack unpack str
