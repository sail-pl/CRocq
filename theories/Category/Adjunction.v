
From Stdlib.Logic Require Import ProofIrrelevance.

From CRocq.Category Require Import Category Functor Transformation.
From CRocq.Category Require Import CategoryCat.

(** ** Adjonctions *)
(** An adjunction between two categories [C] and [D] is a pair 
  of functors [F : Cat C D] and [G : Cat D C] together with a natural
  transformation [iso : NaturalTransformation (idty C) (G ∘ f)]
  *)

Definition Adjunction {C D : Cat} (F : Cat C D) (G : Cat D C) 
  (η : NaturalTransformation (idty C) (G ∘ F)) : Type := 
    forall (x : C) (y : D) (f : C x (G y)),
    exists! (g : D (F x) y), f = (fmap G g) ∘ (η x).
