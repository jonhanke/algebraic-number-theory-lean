import NumberFieldKB.WeilBNT.FunctionField.PlaceSplitting
import NumberFieldKB.WeilBNT.FunctionField.RiemannRochCor

/-!
# The zeta function of a global function field, unconditionally (Weil VII.§6, Thm. 4)

* **`genus Fq k`**: the genus $g\in\mathbb N$ (Weil VI.§2, Def. 1), $g=$ `Rep.genusInt` when $\mathbb F_q$ is the field of
  constants; **`genus_unique`**: it is the only integer for which Riemann–Roch holds with some divisor $\mathfrak c$.
* **`weilZetaCoreInputs`**: the named input `WeilZetaCoreInputs` holds whenever $\mathbb F_q$ is the field
  of constants: Riemann–Roch (`weil_VI_2_thm2`), $D_0/P$ finite (`finite_classGroup0`), a divisor of degree 1
  (`weil_VII_5_cor5_ff`), $\deg\operatorname{div}\xi=0$ (`Divisor.deg_div_eq_zero`).
* **`weil_VII_6_thm4_ff`** (Weil VII.§6, Thm. 4): for a global function field with field of constants $\mathbb F_q$,
  $Z(u)(1-u)(1-qu)=P(u)$ with $P\in\mathbb Z[u]$ of degree $2g$, $P(0)=1$, $P(1)=h$ and $P(u)=q^gu^{2g}P(1/qu)$, where
  $\zeta_k(s)=Z(q^{-s})$. No input is assumed beyond Weil's hypothesis that $\mathbb F_q$ is the field of constants.
-/

open scoped Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

open Divisor Rep

variable (Fq k) in
/-- **The genus** $g$ (Weil VI.§2, Def. 1), as a natural number. -/
@[kb "weil1973bnt" "Ch. VI, Def. 1 (p. 100), the genus, function fields"]
def genus : ℕ := (genusInt Fq k).toNat

theorem genus_eq (hc : IsConstantField Fq k) : (genus Fq k : ℤ) = genusInt Fq k :=
  Int.toNat_of_nonneg (genusInt_nonneg hc)

/-- **Uniqueness of the genus**: if $\lambda(\mathfrak a)=\deg\mathfrak a+1-g'+\lambda(\mathfrak c'-\mathfrak a)$ for
all $\mathfrak a$, then $g'=g$. -/
theorem genus_unique (hc : IsConstantField Fq k) (g' : ℤ) (c' : Divisor Fq k)
    (h : ∀ a : Divisor Fq k, (a.ell : ℤ) = deg a + 1 - g' + (c' - a).ell) : g' = genusInt Fq k := by
  obtain ⟨B, -, hB⟩ := exists_divisor_deg_ge (Fq := Fq) (k := k)
    ((deg c').toNat + 2 * (genusInt Fq k).toNat + 2)
  push_cast at hB
  have hg0 := genusInt_nonneg hc
  have h1 := h B
  have h0 : (c' - B).ell = 0 := ell_eq_zero_of_deg_neg' (by rw [map_sub]; omega)
  have h2 := weil_VI_2_cor2 hc (a := B) (by omega)
  rw [h0] at h1
  push_cast at h1
  omega

/-- **The core inputs of the zeta theorem hold** when $\mathbb F_q$ is the field of constants. -/
theorem weilZetaCoreInputs (hc : IsConstantField Fq k) : WeilZetaCoreInputs Fq k where
  riemannRoch := ⟨genus Fq k, canonical Fq k, fun a => by rw [genus_eq hc]; exact weil_VI_2_thm2 a⟩
  finite_classGroup0 := finite_classGroup0
  exists_deg_one := weil_VII_5_cor5_ff hc
  deg_div := Divisor.deg_div_eq_zero

/-- **The inputs of the zeta theorem hold** (`WeilZetaInputs`, Weil VII.§6, Thm. 4) when $\mathbb F_q$ is the field of
constants, unconditionally: from `weilZetaCoreInputs` (Riemann–Roch `weil_VI_2_thm2`, `finite_classGroup0`,
`weil_VII_5_cor5_ff`, `Divisor.deg_div_eq_zero`). The hypothesis `hc` is needed: if the field of constants is larger
than $\mathbb F_q$, every degree is a multiple of its degree over $\mathbb F_q$ and there is no divisor of degree $1$. -/
@[kb "weil1973bnt" "Ch. VII, §6, Thm. 4 (p. 130), its inputs, function fields, unconditional"]
theorem weilZetaInputs (hc : IsConstantField Fq k) : WeilZetaInputs Fq k :=
  (weilZetaCoreInputs hc).toWeilZetaInputs

theorem genus_weilZetaInputs (hc : IsConstantField Fq k) :
    (weilZetaCoreInputs hc).toWeilZetaInputs.genus = genus Fq k := by
  have hspec := (weilZetaCoreInputs (Fq := Fq) (k := k) hc).toWeilZetaInputs.riemannRoch.choose_spec
  obtain ⟨c', hc'⟩ := hspec
  have := genus_unique hc _ c' hc'
  have h2 := genus_eq (Fq := Fq) (k := k) hc
  unfold WeilZetaInputs.genus
  omega

/-- **Weil VII.§6, Thm. 4** (rationality and functional equation of the zeta function of a global function field
with field of constants $\mathbb F_q$), unconditional. -/
@[kb "weil1973bnt" "Ch. VII, §6, Thm. 4 (p. 130), function fields, unconditional"]
theorem weil_VII_6_thm4_ff (hc : IsConstantField Fq k) :
    ∃ P : ℤ[X], P.natDegree = 2 * genus Fq k ∧ P.eval 0 = 1 ∧
      P.eval 1 = Nat.card (ClassGroup0 Fq k) ∧
      zetaSeries Fq k * ((1 - PowerSeries.X) * (1 - (Nat.card Fq : PowerSeries ℤ) * PowerSeries.X)) =
        (P : PowerSeries ℤ) ∧
      ∀ i ≤ 2 * genus Fq k,
        P.coeff (2 * genus Fq k - i) * (Nat.card Fq : ℤ) ^ i = (Nat.card Fq : ℤ) ^ genus Fq k * P.coeff i := by
  have h := weil_VII_6_thm4 hc (weilZetaCoreInputs hc).toWeilZetaInputs
  rw [genus_weilZetaInputs hc] at h
  exact h

end NumberFieldKB.WeilBNT.FF
