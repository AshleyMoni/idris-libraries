module Ashley.Elem

import Data.List
import Data.Vect

%access public
%default total

||| If an element is in the left sublist of an append, it's in the final list too.
list_elemXs_elemXsYs : {x : a} -> {xs, ys : List a} ->
                       Elem x xs -> Elem x (xs ++ ys)
list_elemXs_elemXsYs Here      = Here
list_elemXs_elemXsYs (There r) = There $ list_elemXs_elemXsYs r

||| If an element is in the right sublist of an append, it's in the final list too.
list_elemXs_elemYsXs : {x : a} -> {xs, ys : List a} ->
                       Elem x xs -> Elem x (ys ++ xs)
list_elemXs_elemYsXs {ys = []}     = id
list_elemXs_elemYsXs {ys = _::ys'} = There . list_elemXs_elemYsXs {ys = ys'}


||| If an element is in the left subvector of an append, it's in the final vector too.
vect_elemXs_elemXsYs : {n, m : Nat} -> {x : a, xs : Vect n a, ys : Vect m a} ->
                       Elem x xs -> Elem x (xs ++ ys)
vect_elemXs_elemXsYs Here      = Here
vect_elemXs_elemXsYs (There r) = There $ vect_elemXs_elemXsYs r

||| If an element is in the right subvector of an append, it's in the final vector too.
vect_elemXs_elemYsXs : {n, m : Nat} -> {x : a, xs : Vect n a, ys : Vect m a} ->
                       Elem x xs -> Elem x (ys ++ xs)
vect_elemXs_elemYsXs {ys = []}     = id
vect_elemXs_elemYsXs {ys = _::ys'} = There . vect_elemXs_elemYsXs {ys = ys'}
