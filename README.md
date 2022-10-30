# Uniplate

This is an idris port of the Haskell [uniplate](https://github.com/ndmitchell/uniplate) library

## Overview

Uniplate is a way to describe traversals over a structure with much less boilerplate as you only need to specify what's relevant.

Unlike the Haskell version, there is a `GetRepr`/`BiGetRepr` function, which makes `uniplate`/`biplate` safer to implement.
