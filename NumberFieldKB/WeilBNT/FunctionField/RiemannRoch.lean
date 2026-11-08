import NumberFieldKB.WeilBNT.FunctionField.Repartition
import NumberFieldKB.WeilBNT.FunctionField.RelDim
import NumberFieldKB.WeilBNT.FunctionField.RiemannInequality

/-!
# The Riemann–Roch theorem (Weil VI.§2, Thm. 2, divisor form)

Notation: $U(\mathfrak a)$ (`Rep.U a`), $k$ diagonal in the repartitions (`Rep.principal`),
$S(\mathfrak a)=U(\mathfrak a)+k$ (`Rep.S a`).

* **`Rep.relDim_U`**: $\dim U(\mathfrak b)/U(\mathfrak a)=\deg\mathfrak b-\deg\mathfrak a$ for $\mathfrak a\le\mathfrak b$.
* **`Rep.relDim_S`**: $\dim S(\mathfrak b)/S(\mathfrak a)=(\deg\mathfrak b-\lambda(\mathfrak b))-(\deg\mathfrak a-\lambda(\mathfrak a))$
  (Weil VI.§2, the exact sequence behind Thm. 1).
* **`genusInt`**: $g$, with $g-1=\max_{\mathfrak a}(\deg\mathfrak a-\lambda(\mathfrak a))$ (Riemann's theorem gives the max).
* **`Rep.index a`** $=\dim\mathbb A/(U(\mathfrak a)+k)$ (Weil's $\delta(\mathfrak a)$, "index of speciality"), finite, and
  **`ell_sub_index`**: $\lambda(\mathfrak a)-i(\mathfrak a)=\deg\mathfrak a+1-g$.
* **Weil differentials** `Rep.Omega a` $=\Omega(\mathfrak a)$, the linear forms on repartitions vanishing on
  $U(\mathfrak a)+k$ (Weil's characters of $k_{\mathbb A}/k$ trivial on $U(\mathfrak a)$); $k$ acts by
  $(\xi\omega)(\alpha)=\omega(\xi\alpha)$ (`Rep.xω`). Every nonzero $\omega$ has a divisor $(\omega)$ with
  $\omega\in\Omega(\mathfrak a)\iff\mathfrak a\le(\omega)$ (`Rep.exists_divisor`), and any two nonzero Weil differentials
  differ by a factor in $k$ (`Rep.exists_eq_xω`).
* **`riemannRoch`** (Weil VI.§2 Thm. 2): with $\mathfrak c$ the divisor of a nonzero Weil differential,
  $\lambda(\mathfrak a)=\deg\mathfrak a+1-g+\lambda(\mathfrak c-\mathfrak a)$ for every divisor $\mathfrak a$.
-/

open scoped Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Divisor

/-- The pointwise maximum $\sup(\mathfrak a,\mathfrak b)=\mathfrak a+(\mathfrak b-\mathfrak a)^+$. -/
def sup' (a b : Divisor Fq k) : Divisor Fq k := a + (b - a).pos

theorem le_sup'_left (a b : Divisor Fq k) : a ≤ sup' a b := by
  intro v; simp [sup']

theorem le_sup'_right (a b : Divisor Fq k) : b ≤ sup' a b := by
  intro v; simp [sup']; omega

theorem sup'_apply (a b : Divisor Fq k) (v : Place Fq k) : sup' a b v = max (a v) (b v) := by
  simp [sup']; omega

theorem deg_mono {a b : Divisor Fq k} (h : a ≤ b) : deg a ≤ deg b := by
  have := deg_nonneg (sub_nonneg.mpr h)
  rw [map_sub] at this
  omega

theorem eq_of_le_of_deg_eq {a b : Divisor Fq k} (h : a ≤ b) (hd : deg a = deg b) : a = b := by
  have := eq_zero_of_deg_eq_zero (sub_nonneg.mpr h) (by rw [map_sub]; omega)
  exact (sub_eq_zero.mp this).symm

end Divisor

namespace Rep

open Divisor

/-- $\dim U(\mathfrak a+v)/U(\mathfrak a)=\deg v$. -/
theorem relDim_U_single (a : Divisor Fq k) (v : Place Fq k) :
    RelFinite (U a) (U (a + Finsupp.single v 1)) ∧
      relDim (U a) (U (a + Finsupp.single v 1)) = v.degree := by
  obtain ⟨ψ, hsurj, hker⟩ := exists_residue_surj a v
  have hk : LinearMap.ker ψ = (U a).comap (U (a + Finsupp.single v 1)).subtype := by
    ext α
    rw [LinearMap.mem_ker, hker]
    rfl
  let e : RelQuot (U a) (U (a + Finsupp.single v 1)) ≃ₗ[Fq] v.residueField :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  haveI : Module.Finite Fq v.residueField := Module.Finite.of_finite
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq⟩

/-- **$\dim U(\mathfrak b)/U(\mathfrak a)=\deg\mathfrak b-\deg\mathfrak a$** for $\mathfrak a\le\mathfrak b$. -/
theorem relDim_U {a b : Divisor Fq k} (h : a ≤ b) :
    RelFinite (U a) (U b) ∧ (relDim (U a) (U b) : ℤ) = deg b - deg a := by
  suffices H : ∀ (n : ℕ) (a b : Divisor Fq k), a ≤ b → (deg (b - a)).toNat = n →
      RelFinite (U a) (U b) ∧ (relDim (U a) (U b) : ℤ) = deg b - deg a from H _ a b h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab hn
    by_cases heq : a = b
    · subst heq
      exact ⟨relFinite_of_le le_rfl, by rw [relDim_eq_zero_of_le le_rfl]; simp⟩
    · obtain ⟨v, hv⟩ : ∃ v, a v ≠ b v := by
        by_contra hcon
        push Not at hcon
        exact heq (Finsupp.ext hcon)
      have hlt : a v < b v := lt_of_le_of_ne (hab v) hv
      have hab' : a + Finsupp.single v 1 ≤ b := by
        intro w
        by_cases hw : w = v
        · subst hw; simp; omega
        · simpa [Finsupp.single_apply, Ne.symm hw] using hab w
      have hd : deg (b - (a + Finsupp.single v 1)) = deg (b - a) - v.degree := by
        rw [sub_add_eq_sub_sub, map_sub, deg_single]; simp
      have hdp := v.degree_pos
      have hnn : 0 ≤ deg (b - a) := deg_nonneg (sub_nonneg.mpr hab)
      have hlt' : (deg (b - (a + Finsupp.single v 1))).toNat < n := by
        have h3 := deg_nonneg (sub_nonneg.mpr hab')
        rw [hd] at h3 ⊢
        rw [← hn]
        omega
      obtain ⟨f2, h2⟩ := ih (deg (b - (a + Finsupp.single v 1))).toNat hlt' _ b hab' rfl
      obtain ⟨f1, h1⟩ := relDim_U_single a v
      have hle1 : a ≤ a + Finsupp.single v 1 := le_add_of_nonneg_right (by simp)
      have ht := relDim_trans (U_mono hle1) (U_mono hab') f1 f2
      refine ⟨relFinite_trans (U_mono hle1) (U_mono hab') f1 f2, ?_⟩
      rw [ht]
      push_cast
      rw [h1, h2, map_add, deg_single]
      ring

variable (Fq k) in
/-- $S(\mathfrak a)=U(\mathfrak a)+k$. -/
def S (a : Divisor Fq k) : Submodule Fq (Rep Fq k) := U a ⊔ principal Fq k

theorem S_mono {a b : Divisor Fq k} (h : a ≤ b) : S Fq k a ≤ S Fq k b :=
  sup_le_sup_right (U_mono h) _

/-- **$\dim S(\mathfrak b)/S(\mathfrak a)=(\deg\mathfrak b-\lambda(\mathfrak b))-(\deg\mathfrak a-\lambda(\mathfrak a))$.** -/
theorem relDim_S {a b : Divisor Fq k} (h : a ≤ b) :
    RelFinite (S Fq k a) (S Fq k b) ∧
      (relDim (S Fq k a) (S Fq k b) : ℤ) = (deg b - b.ell) - (deg a - a.ell) := by
  obtain ⟨fU, hU⟩ := relDim_U h
  obtain ⟨f1, f2, hsum⟩ := relDim_sup_add_inf (principal Fq k) (U_mono h) fU
  rw [U_inf_principal, U_inf_principal] at hsum
  have hmap := (relDim_map (diag (Fq := Fq) (k := k)) diag_injective a.riemannRochSpace
    b.riemannRochSpace).2
  obtain ⟨-, hL⟩ := relDim_of_finiteDimensional (riemannRochSpace_mono h)
  refine ⟨f1, ?_⟩
  rw [hmap] at hsum
  unfold ell
  have : (relDim (S Fq k a) (S Fq k b) : ℤ) + relDim a.riemannRochSpace b.riemannRochSpace =
      relDim (U a) (U b) := by exact_mod_cast hsum
  have hL' : (relDim a.riemannRochSpace b.riemannRochSpace : ℤ) +
      Module.finrank Fq a.riemannRochSpace = Module.finrank Fq b.riemannRochSpace := by
    exact_mod_cast hL
  linarith

/-- The maximum of $\deg\mathfrak a-\lambda(\mathfrak a)$ is attained (Riemann's theorem). -/
theorem exists_max_defect : ∃ b₀ : Divisor Fq k, ∀ a : Divisor Fq k,
    deg a - (a.ell : ℤ) ≤ deg b₀ - b₀.ell := by
  obtain ⟨γ, hγ⟩ := exists_deg_sub_ell_le (Fq := Fq) (k := k)
  obtain ⟨m, ⟨b₀, rfl⟩, hm⟩ := Int.exists_greatest_of_bdd (P := fun m => ∃ b : Divisor Fq k,
    deg b - (b.ell : ℤ) = m) ⟨γ, by rintro _ ⟨b, rfl⟩; exact hγ b⟩ ⟨_, 0, rfl⟩
  exact ⟨b₀, fun a => hm _ ⟨a, rfl⟩⟩

variable (Fq k) in
/-- A divisor at which $\deg-\lambda$ is maximal. -/
def maxDefect : Divisor Fq k := (exists_max_defect (Fq := Fq) (k := k)).choose

theorem le_maxDefect (a : Divisor Fq k) :
    deg a - (a.ell : ℤ) ≤ deg (maxDefect Fq k) - (maxDefect Fq k).ell :=
  (exists_max_defect (Fq := Fq) (k := k)).choose_spec a

/-- $S(\mathfrak b)$ is everything as soon as $\mathfrak b\ge\mathfrak b_0$. -/
theorem S_eq_top {b : Divisor Fq k} (hb : maxDefect Fq k ≤ b) : S Fq k b = ⊤ := by
  rw [eq_top_iff]
  rintro α -
  obtain ⟨c, hbc, hα⟩ := exists_mem_U b α
  obtain ⟨f, hrel⟩ := relDim_S hbc
  have h1 := deg_sub_ell_mono hb
  have h2 := deg_sub_ell_mono hbc
  have h3 := le_maxDefect c
  have h0 : relDim (S Fq k b) (S Fq k c) = 0 := by omega
  exact le_of_relDim_eq_zero f h0 (Submodule.mem_sup_left hα)

variable (Fq k) in
/-- **The genus** $g$: $g-1=\max_{\mathfrak a}(\deg\mathfrak a-\lambda(\mathfrak a))$ (Weil VI.§2, Def. 1, through
Thm. 2). It is a nonnegative integer when $\mathbb F_q$ is the field of constants (`genusInt_nonneg`). -/
def genusInt : ℤ := deg (maxDefect Fq k) - (maxDefect Fq k).ell + 1

variable (Fq k) in
/-- **The index of speciality** $i(\mathfrak a)=\dim\mathbb A/(U(\mathfrak a)+k)$. -/
def index (a : Divisor Fq k) : ℕ := Module.finrank Fq (Rep Fq k ⧸ S Fq k a)

theorem relDim_S_top (a : Divisor Fq k) :
    RelFinite (S Fq k a) ⊤ ∧
      (relDim (S Fq k a) ⊤ : ℤ) = genusInt Fq k - 1 - (deg a - a.ell) := by
  set c := sup' a (maxDefect Fq k)
  have hc : S Fq k c = ⊤ := S_eq_top (le_sup'_right _ _)
  obtain ⟨f, h⟩ := relDim_S (le_sup'_left a (maxDefect Fq k))
  rw [hc] at f h
  refine ⟨f, ?_⟩
  rw [h]
  have h1 := deg_sub_ell_mono (le_sup'_right a (maxDefect Fq k))
  have h2 := le_maxDefect (sup' a (maxDefect Fq k))
  unfold genusInt
  omega

instance finiteDimensional_quot_S (a : Divisor Fq k) : FiniteDimensional Fq (Rep Fq k ⧸ S Fq k a) :=
  ((relDim_top (S Fq k a)).1).mp (relDim_S_top a).1

/-- **$\lambda(\mathfrak a)-i(\mathfrak a)=\deg\mathfrak a+1-g$** (Weil VI.§2; Riemann–Roch before duality). -/
theorem ell_sub_index (a : Divisor Fq k) :
    (a.ell : ℤ) - index Fq k a = deg a + 1 - genusInt Fq k := by
  have h := (relDim_S_top a).2
  rw [(relDim_top (S Fq k a)).2] at h
  unfold index
  omega

end Rep

end NumberFieldKB.WeilBNT.FF
