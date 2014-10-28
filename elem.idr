module Ashley.Elem

import Data.List

%access public
%default total

||| If an element is in the left sublist of an append, it's in the final list too.
elemXs_elemXsYs : {x : a} -> {xs, ys : List a} -> Elem x xs -> Elem x (xs ++ ys)
elemXs_elemXsYs Here      = Here
elemXs_elemXsYs (There r) = There $ elemXs_elemXsYs r

||| If an element is in the right sublist of an append, it's in the final list too.
elemXs_elemYsXs : {x : a} -> {xs, ys : List a} -> Elem x xs -> Elem x (ys ++ xs)
elemXs_elemYsXs {ys = []}     = id
elemXs_elemYsXs {ys = _::ys'} = There . elemXs_elemYsXs {ys = ys'}
