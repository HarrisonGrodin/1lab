<!--
```agda
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Instances.Product
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Product
open import Cat.Instances.Functor
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Functor.Compose
open import Cat.Monoidal.Base
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Diagram.Monad
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Monad.Instances.Writer
  {o ℓ} {C : Precategory o ℓ}
  (terminal : Terminal C)
  (products : ∀ A B → Product C A B)
  (A : Precategory.Ob C) (A-monoid : Monoid-on (Cartesian-monoidal products terminal) A)
  where

open Monoid-on
open Precategory C
open Terminal
open Monad
open _=>_

Cat[C,C]-terminal : Terminal Cat[ C , C ]
Cat[C,C]-terminal .top = Const (terminal .top)
Cat[C,C]-terminal .has⊤ F = contr (NT (λ _ → ! terminal) λ x y f → {!   !}) {!   !}

Cat[C,C]-products : ∀ F G → Product Cat[ C , C ] F G
Cat[C,C]-products F G = product where
  open Product
  open Binary-products C products

  product : Product Cat[ C , C ] F G
  product .apex = ×-functor F∘ Cat⟨ F , G ⟩
  product .π₁ = {!   !}
  product .π₂ = {!   !}
  product .has-is-product = {!   !}
    -- Limit→Product
    --   Cat[ C , C ]
    --   (functor-limit {!   !} (2-object-diagram Cat[ C , C ] F G))

open Product (Cat[C,C]-products (Const A) Id)

writer-monad : Monad C
writer-monad .M = apex
writer-monad .unit =
  ⟨ const-nt (A-monoid .η) ∘nt Terminal.! Cat[C,C]-terminal
  , idnt
  ⟩
writer-monad .mult =
  ⟨ const-nt (A-monoid .μ) ∘nt {!   !} -- subst (apex F∘ apex =>_) {!   !} ⟨ {! π₁  !} , {!   !} ⟩
  , subst (apex F∘ apex =>_) F∘-idl (π₂ ◆ π₂)
  ⟩
writer-monad .left-ident = {! _◆_  !}
writer-monad .right-ident = {! subst  !}
writer-monad .mult-assoc = {!   !}
```
