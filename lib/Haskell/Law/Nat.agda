module Haskell.Law.Nat where

open import Haskell.Law.Equality
open import Haskell.Prim renaming (addNat to _+_)

suc-injective : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-injective refl = refl

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-assoc : ∀ n m o → n + m + o ≡ n + (m + o)
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

+-identity-left : ∀ n → (0 + n) ≡ n
+-identity-left _ = refl

+-identity-right : ∀ n → (n + 0) ≡ n
+-identity-right zero    = refl
+-identity-right (suc n) = cong suc (+-identity-right n)

+-comm : ∀ n m → n + m ≡ m + n
+-comm zero    n = sym (+-identity-right n)
+-comm (suc m) n = begin
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩
  n + suc m   ∎

+-cancel-left : ∀ n m o → n + m ≡ n + o → m ≡ o
+-cancel-left zero    _ _ eq = eq
+-cancel-left (suc m) _ _ eq = +-cancel-left m _ _ (cong pred eq)

+-cancel-right : ∀ n m o → n + m ≡ o + m → n ≡ o
+-cancel-right n m o 
  rewrite +-comm n m | +-comm o m = +-cancel-left m n o

0≠1+n : ∀ {n} → 0 ≠ suc n
0≠1+n ()

1+n≠0 : ∀ {n} → suc n ≠ 0
1+n≠0 ()

1+n≠n : ∀ {n} → suc n ≠ n
1+n≠n {suc n} = 1+n≠n ∘ suc-injective

m≠1+m+n : ∀ m {n} → m ≠ suc (m + n)
m≠1+m+n (suc m) eq = m≠1+m+n m (cong pred eq)

m≠1+n+m : ∀ m {n} → m ≠ suc (n + m)
m≠1+n+m m h = m≠1+m+n m (trans h (cong suc (+-comm _ m)))