import LeanCond.Reals.Dedekind.Basic
import LeanCond.Reals.Eudoxus.Basic

namespace PreEudoxus

def toDedekind (x : PreEudoxus) : Dedekind where
  L q := ∃ N : ℕ, ∀ n : ℕ, n ≥ N → q * n < x.1 n
  U q := ∃ N : ℕ, ∀ n : ℕ, n ≥ N → x.1 n < q * n
  finite := by sorry
  L_mono {q₁ q₂} h := by
    rintro ⟨N, hN⟩
    use N
    intro n hn
    refine lt_of_le_of_lt ?_ (hN n hn)
    exact mul_le_mul_of_nonneg_right h n.cast_nonneg
  U_mono {q₁ q₂} h := by
    rintro ⟨N, hN⟩
    use N
    intro n hn
    refine lt_of_lt_of_le (hN n hn) ?_
    exact mul_le_mul_of_nonneg_right h n.cast_nonneg
  L_rounded {q} := by
    rintro ⟨N, hN⟩
    sorry
  U_rounded {q} := by
    rintro ⟨N, hN⟩
    sorry
  located {q₁ q₂} h := by sorry
  disjoint {q} := by
    rintro ⟨⟨N, hN⟩, ⟨N', hN'⟩⟩
    let n := max N N'
    specialize hN n (le_max_left _ _)
    specialize hN' n (le_max_right _ _)
    exact lt_irrefl (q * n) (hN.trans hN')

end PreEudoxus
