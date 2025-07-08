Require Import CRocq.Category.Category.
Require Import CRocq.Category.Functor.
Require Import CRocq.Category.Transformation.

Class Cone {J C : Category} (D : Functor J C) (c : C) : Type := {
    apex := c;
    cone_obj : NaturalTransformation (ConstantFunctor J C c) D
}.

Coercion cone_obj : Cone >-> NaturalTransformation.

Class CoCone {J C : Category} (D : Functor J C) (c : C) : Type := {
    coapex := c;
    cocone_obj : NaturalTransformation D (ConstantFunctor J C c)
}.

Coercion cocone_obj : CoCone >-> NaturalTransformation.
