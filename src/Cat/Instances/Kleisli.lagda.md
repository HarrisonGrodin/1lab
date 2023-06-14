<!--
```agda
open import Cat.Diagram.Monad
open import Cat.Diagram.Monad.Solver
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Equivalence
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Kleisli {o h : _} {C : Precategory o h} (M : Monad C) where

import Cat.Reasoning C as C
```

```agda
private
  module M = Monad M
open M hiding (M)
open Precategory

_† : {X Y : C .Ob} → C .Hom X (M₀ Y) → C .Hom (M₀ X) (M₀ Y)
f † = M.mult.η _ C.∘ M₁ f

Kleisli : Precategory o h
Kleisli .Ob = C .Ob
Kleisli .Hom X Y = C .Hom X (M₀ Y)
Kleisli .id = M.unit.η _
Kleisli ._∘_ g f = (g †) C.∘ f
Kleisli .idr f = {! monad! M  !}
Kleisli .idl f = {! monad! M  !}
Kleisli .assoc f g h = {! monad! M  !}
Kleisli .Hom-set X Y = C .Hom-set _ _
```

```agda
open Functor

is-free : Algebra C M → Type (o ⊔ h)
is-free X = Σ[ A ∈ C .Ob ] (X ≡ F₀ (Free C M) A)

Kleisli-full-subcategory : Equivalence Kleisli (Restrict {C = Eilenberg-Moore C M} is-free)
Kleisli-full-subcategory = equivalence where
  open Equivalence
  open is-equivalence
  open Algebra-hom

  equivalence : Equivalence Kleisli (Restrict {C = Eilenberg-Moore C M} is-free)
  equivalence .To .F₀ A = restrict (F₀ (Free C M) A) (A , refl)
  equivalence .To .F₁ f .morphism = f †
  equivalence .To .F₁ f .commutes = {!   !}
  equivalence .To .F-id = {! monad! M  !}
  equivalence .To .F-∘ g f = {! monad! M  !}
  equivalence .To-equiv .F⁻¹ .F₀ X = X .object .fst
  equivalence .To-equiv .F⁻¹ .F₁ m = M.unit.η _ C.∘ m .morphism
  equivalence .To-equiv .F⁻¹ .F-id = {!   !}
  equivalence .To-equiv .F⁻¹ .F-∘ = {!   !}
  equivalence .To-equiv .F⊣F⁻¹ = {!   !}
  equivalence .To-equiv .unit-iso = {!   !}
  equivalence .To-equiv .counit-iso = {!   !}
```
