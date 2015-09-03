module Lists where

import qualified Prelude

my_last :: ([] a1) -> Prelude.Maybe a1
my_last xs =
  case xs of {
   [] -> Prelude.Nothing;
   (:) x xt ->
    case xt of {
     [] -> Prelude.Just x;
     (:) x0 l -> my_last xt}}

