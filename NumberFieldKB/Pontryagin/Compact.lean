import NumberFieldKB.Pontryagin.Discrete
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Pontryagin duality for compact commutative groups, given the Peter–Weyl theorem

**Named input.** `PeterWeylTheorem`: the finite-dimensional continuous representations of a compact Hausdorff group
separate its points. This is proved in Tau Ceti (`TauCeti.exists_contRepresentation_apply_ne`,
`TauCeti/RepresentationTheory/Compact/RepresentativeDensity.lean`, Tau Ceti main `7ed979d`, 2026-11-04; Tau Ceti's
`ContRepresentation ℂ G V` is a wrapper of `G →* (V →L[ℂ] V)` and its `Continuous π` is continuity for the operator
norm, as here). Tau Ceti cannot be imported here (toolchain v4.36 against our v4.35), so the theorem is cited, not
re-proved. It is not the conclusion: it speaks of matrix representations, not of characters.

Proved here from it:
* `charactersSeparate_of_rep`: for a **commutative** compact group, a continuous finite-dimensional representation
  $\pi$ with $\pi(g)\ne1$ yields a character $\chi$ with $\chi(g)\ne1$. Proof: the operators $\pi(h)$ commute, so the
  simultaneous generalized eigenspaces span (Mathlib,
  `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`); $\pi(G)$ is bounded,
  so the eigenvalues have absolute value $1$ and there are no Jordan blocks ($\pi(h)^k u=c^ku+kc^{k-1}Nu$ would be
  unbounded); hence on each simultaneous eigenspace $\pi(h)$ acts by a scalar $\chi(h)$, a continuous character.
* `charactersSeparate_of_compact`: the characters of a compact commutative Hausdorff group separate points.
* **`pontryaginDuality_compact`**: for a compact commutative Hausdorff group $G$, $G\to G^{**}$ is an isomorphism of
  topological groups. Injective by separation; onto: the image $H$ is compact, and a character of $G^{**}$ trivial on
  $H$ (from separation on $G^{**}/H$) is evaluation at some $\chi\in G^*$ (duality for the discrete group $G^*$),
  necessarily $\chi=1$; a continuous bijection from a compact space to a Hausdorff space is a homeomorphism.
-/

open Topology Module

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

/-- **Named input: the Peter–Weyl theorem** (point separation form), for compact Hausdorff groups in universe `u`.
Cited from Tau Ceti: `TauCeti.exists_contRepresentation_apply_ne` (with `𝕜 = ℂ`). -/
structure PeterWeylTheorem : Prop where
  separates : ∀ (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    (x y : K), x ≠ y → ∃ (n : ℕ) (π : K →* (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))),
      Continuous π ∧ π x ≠ π y

section PowerBounded

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- If $N^2u=0$ for $N=A-c$, then $A^{k+1}u=c^{k+1}u+(k+1)c^kNu$. -/
lemma pow_succ_apply_of_sq (A : End ℂ V) (c : ℂ) (u : V) (h2 : (A - c • 1) ((A - c • 1) u) = 0) (k : ℕ) :
    (A ^ (k + 1)) u = c ^ (k + 1) • u + (((k : ℂ) + 1) * c ^ k) • (A - c • 1) u := by
  have hAu : A u = c • u + (A - c • 1) u := by simp
  have hANu : A ((A - c • 1) u) = c • (A - c • 1) u := by
    have : A ((A - c • 1) u) = c • (A - c • 1) u + (A - c • 1) ((A - c • 1) u) := by simp
    rw [this, h2, add_zero]
  induction k with
  | zero => simpa using hAu
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul, hAu, hANu]
    simp only [smul_add, smul_smul]
    push_cast
    rw [pow_succ c (k + 1), pow_succ c k]
    module

/-- **No Jordan blocks for a power-bounded operator**: if $\|A^k\|$ is bounded, $|c|=1$ and $(A-c)^mv=0$, then
$Av=cv$. -/
lemma apply_eq_smul_of_bounded (A : End ℂ V) (c : ℂ) (hc : ‖c‖ = 1) (C : ℝ)
    (hA : ∀ (k : ℕ) (v : V), ‖(A ^ k) v‖ ≤ C * ‖v‖) :
    ∀ (m : ℕ) (v : V), ((A - c • 1) ^ m) v = 0 → (A - c • 1) v = 0 := by
  set N := A - c • 1 with hN
  -- the key step: `N (N u) = 0 → N u = 0`
  have key : ∀ u : V, N (N u) = 0 → N u = 0 := by
    intro u hu
    by_contra hne
    have hpos : 0 < ‖N u‖ := norm_pos_iff.mpr hne
    obtain ⟨k, hk⟩ := exists_nat_gt ((C * ‖u‖ + ‖u‖) / ‖N u‖)
    have h1 := pow_succ_apply_of_sq A c u hu k
    have h2 : ‖(((k : ℂ) + 1) * c ^ k) • N u‖ ≤ C * ‖u‖ + ‖u‖ := by
      have : (((k : ℂ) + 1) * c ^ k) • N u = (A ^ (k + 1)) u - c ^ (k + 1) • u := by
        rw [h1]; abel
      rw [this]
      calc ‖(A ^ (k + 1)) u - c ^ (k + 1) • u‖ ≤ ‖(A ^ (k + 1)) u‖ + ‖c ^ (k + 1) • u‖ := norm_sub_le _ _
        _ ≤ C * ‖u‖ + ‖u‖ := by
          gcongr
          · exact hA _ _
          · rw [norm_smul, norm_pow, hc, one_pow, one_mul]
    rw [norm_smul, norm_mul, norm_pow, hc, one_pow, mul_one] at h2
    have h3 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
    rw [h3] at h2
    rw [div_lt_iff₀ hpos] at hk
    nlinarith
  intro m
  induction m with
  | zero => intro v hv; simp at hv; simp [hv]
  | succ m ih =>
    intro v hv
    rcases m with _ | m
    · simpa using hv
    · have hu : N (N ((N ^ m) v)) = 0 := by
        simpa only [pow_succ', Module.End.mul_apply] using hv
      have := key _ hu
      apply ih
      rw [pow_succ', Module.End.mul_apply]
      exact this

/-- A non-zero vector killed by a power of $N$ gives a non-zero vector killed by $N$. -/
lemma exists_ne_zero_apply_eq_zero (N : End ℂ V) :
    ∀ (m : ℕ) (v : V), v ≠ 0 → (N ^ m) v = 0 → ∃ u, u ≠ 0 ∧ N u = 0 := by
  intro m
  induction m with
  | zero => intro v hv h; simp at h; exact absurd h hv
  | succ m ih =>
    intro v hv h
    by_cases hN : N v = 0
    · exact ⟨v, hv, hN⟩
    · rw [pow_succ, Module.End.mul_apply] at h
      exact ih _ hN h

/-- An eigenvalue of an operator with bounded powers has absolute value at most $1$. -/
lemma norm_le_one_of_eigen (A : End ℂ V) (c : ℂ) (C : ℝ) (hA : ∀ (k : ℕ) (v : V), ‖(A ^ k) v‖ ≤ C * ‖v‖)
    (u : V) (hu : u ≠ 0) (hAu : A u = c • u) : ‖c‖ ≤ 1 := by
  have hpow : ∀ k : ℕ, (A ^ k) u = c ^ k • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hAu, smul_smul, pow_succ, mul_comm]
  by_contra hlt
  push Not at hlt
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hbound : ∀ k : ℕ, ‖c‖ ^ k ≤ C := by
    intro k
    have := hA k u
    rw [hpow, norm_smul, norm_pow] at this
    exact le_of_mul_le_mul_right this hupos
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hlt
  exact absurd (hbound k) (not_le.mpr hk)

end PowerBounded

section Reduction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- **The abelian reduction.** For a compact commutative group, a continuous finite-dimensional representation
$\pi$ with $\pi(g)\ne1$ gives a character $\chi$ with $\chi(g)\ne1$. -/
theorem exists_char_of_rep {n : ℕ}
    (π : G →* (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) (hπ : Continuous π) (g : G)
    (hg : π g ≠ 1) : ∃ χ : PontryaginDual G, χ g ≠ 1 := by
  set V := EuclideanSpace ℂ (Fin n)
  let f : G → End ℂ V := fun h => ((π h : V →L[ℂ] V) : V →ₗ[ℂ] V)
  have hf_mul : ∀ a b : G, f (a * b) = f a * f b := by
    intro a b; simp only [f, map_mul]; rfl
  have hf_one : f 1 = 1 := by simp only [f, map_one]; rfl
  have hcomm : Pairwise fun a b => Commute (f a) (f b) := by
    intro a b _
    change f a * f b = f b * f a
    rw [← hf_mul, ← hf_mul, mul_comm]
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f hcomm
    (fun h => Module.End.iSup_maxGenEigenspace_eq_top (f h))
  -- uniform bound on the operators
  obtain ⟨C, hC⟩ : ∃ C, ∀ x : G, ‖π x‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hπ.continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  have hfpow : ∀ (h : G) (k : ℕ), f h ^ k = f (h ^ k) := by
    intro h k
    induction k with
    | zero => simp [hf_one]
    | succ k ih => rw [pow_succ, ih, ← hf_mul, ← pow_succ]
  have hbound : ∀ (h : G) (k : ℕ) (v : V), ‖(f h ^ k) v‖ ≤ C * ‖v‖ := by
    intro h k v
    rw [hfpow]
    exact ((π (h ^ k)).le_opNorm v).trans (by gcongr; exact hC _)
  by_contra hall
  push Not at hall
  -- every simultaneous generalized eigenspace is fixed by `π g`
  have hsub : ∀ χ : G → ℂ, (⨅ h, (f h).maxGenEigenspace (χ h)) ≤ LinearMap.ker (f g - 1) := by
    intro χ v hv
    rw [Module.End.mem_iInf_maxGenEigenspace_iff] at hv
    by_cases hv0 : v = 0
    · simp [hv0]
    -- eigenvalues have absolute value one
    have hnorm : ∀ h, ‖χ h‖ = 1 := by
      intro h
      obtain ⟨m, hm⟩ := hv h
      obtain ⟨u, hu0, hu⟩ := exists_ne_zero_apply_eq_zero (f h - χ h • 1) m v hv0 hm
      have hAu : f h u = χ h • u := by
        have := hu; simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
        exact sub_eq_zero.mp this
      have hle := norm_le_one_of_eigen (f h) (χ h) C (hbound h) u hu0 hAu
      have hne0 : χ h ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hAu
        apply hu0
        have : f h⁻¹ (f h u) = u := by rw [← Module.End.mul_apply, ← hf_mul, inv_mul_cancel, hf_one]; rfl
        rw [hAu, map_zero] at this
        exact this.symm
      have hAu' : f h⁻¹ u = (χ h)⁻¹ • u := by
        have : f h⁻¹ (f h u) = u := by rw [← Module.End.mul_apply, ← hf_mul, inv_mul_cancel, hf_one]; rfl
        rw [hAu, map_smul] at this
        rw [← this, smul_smul, inv_mul_cancel₀ hne0, one_smul, this]
      have hle' := norm_le_one_of_eigen (f h⁻¹) (χ h)⁻¹ C (hbound h⁻¹) u hu0 hAu'
      rw [norm_inv] at hle'
      have hpos : 0 < ‖χ h‖ := norm_pos_iff.mpr hne0
      have : 1 ≤ ‖χ h‖ := by
        rw [inv_le_one₀ hpos] at hle'; exact hle'
      linarith
    -- no Jordan blocks: `v` is a common eigenvector
    have heig : ∀ h, f h v = χ h • v := by
      intro h
      obtain ⟨m, hm⟩ := hv h
      have := apply_eq_smul_of_bounded (f h) (χ h) (hnorm h) C (hbound h) m v hm
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact sub_eq_zero.mp this
    -- `χ` is a continuous character
    have hmul : ∀ a b, χ (a * b) = χ a * χ b := by
      intro a b
      have h1 : f (a * b) v = (χ a * χ b) • v := by
        rw [hf_mul, Module.End.mul_apply, heig b, map_smul, heig a, smul_smul, mul_comm]
      rw [heig (a * b)] at h1
      by_contra hne
      have : (χ (a * b) - χ a * χ b) • v = 0 := by rw [sub_smul, h1, sub_self]
      exact hv0 ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne))
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (PiLp.ext fun i => by simpa using hcon i)
    have hcont : Continuous χ := by
      have hform : χ = fun h => (f h v) i / v i := by
        funext h; rw [heig h, PiLp.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hi]
      rw [hform]
      have : Continuous fun h => (π h) v := hπ.clm_apply continuous_const
      exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp this).div_const _
    let χc : PontryaginDual G :=
      { toFun := fun h => ⟨χ h, mem_sphere_zero_iff_norm.mpr (hnorm h)⟩
        map_one' := by
          apply Circle.ext
          show χ 1 = 1
          have h := hmul 1 1
          rw [one_mul] at h
          have hn : χ 1 ≠ 0 := by
            intro h0; have := hnorm 1; rw [h0, norm_zero] at this; exact zero_ne_one this
          have : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, ← h, mul_one, sub_self]
          rcases mul_eq_zero.mp this with h0 | h0
          · exact absurd h0 hn
          · exact sub_eq_zero.mp h0
        map_mul' := fun a b => Circle.ext (by show χ (a * b) = χ a * χ b; exact hmul a b)
        continuous_toFun := by
          apply Continuous.subtype_mk hcont }
    have hg1 : χ g = 1 := by
      have := hall χc
      exact congrArg (fun z : Circle => (z : ℂ)) this
    rw [LinearMap.mem_ker, LinearMap.sub_apply, heig g, hg1, one_smul, Module.End.one_apply, sub_self]
  have : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (f g - 1) := by
    rw [← htop]; exact iSup_le hsub
  apply hg
  ext1 v
  have hv := this (Submodule.mem_top (x := v))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv

end Reduction

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]

/-- **The characters of a compact commutative Hausdorff group separate points** (given the Peter–Weyl theorem). -/
theorem charactersSeparate_of_compact (hPW : PeterWeylTheorem.{u}) : CharactersSeparate G := by
  intro g hg
  obtain ⟨n, π, hπ, hne⟩ := hPW.separates G g 1 hg
  exact exists_char_of_rep π hπ g (by rwa [map_one] at hne)

/-- **Pontryagin duality for compact commutative groups** (given the Peter–Weyl theorem): for a compact commutative
Hausdorff group $G$, $G\to G^{**}$ is an isomorphism of topological groups. -/
theorem pontryaginDuality_compact (hPW : PeterWeylTheorem.{u}) : PontryaginDualityStatement G := by
  have hinj : Function.Injective (dualEval G) :=
    dualEval_injective_iff.mpr (charactersSeparate_of_compact hPW)
  have hsurj : Function.Surjective (dualEval G) := by
    intro ψ
    by_contra hψ
    push Not at hψ
    let H : Subgroup (PontryaginDual (PontryaginDual G)) := (dualEval G).toMonoidHom.range
    have hHc : IsCompact (H : Set (PontryaginDual (PontryaginDual G))) := by
      have : (H : Set (PontryaginDual (PontryaginDual G))) = Set.range (dualEval G) := rfl
      rw [this]
      exact isCompact_range (dualEval G).continuous
    have : IsClosed (H : Set (PontryaginDual (PontryaginDual G))) := hHc.isClosed
    have hψH : (QuotientGroup.mk ψ : PontryaginDual (PontryaginDual G) ⧸ H) ≠ 1 := by
      rw [ne_eq, QuotientGroup.eq_one_iff]
      rintro ⟨g, hg⟩
      exact hψ g (show dualEval G g = ψ from hg)
    obtain ⟨χq, hχq⟩ := charactersSeparate_of_compact (G := PontryaginDual (PontryaginDual G) ⧸ H) hPW _ hψH
    let Φ : PontryaginDual (PontryaginDual (PontryaginDual G)) := χq.comp ⟨QuotientGroup.mk' H, continuous_quot_mk⟩
    -- duality for the discrete group `G*`
    obtain ⟨χ, hχ⟩ := (pontryaginDuality_discrete (G := PontryaginDual G)).choose_spec ▸
      (pontryaginDuality_discrete (G := PontryaginDual G)).choose.surjective Φ
    have hχ1 : χ = 1 := by
      ext g
      have hmem : QuotientGroup.mk' H (dualEval G g) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
      have h1 : Φ (dualEval G g) = 1 := by
        show χq (QuotientGroup.mk' H (dualEval G g)) = 1
        rw [hmem, map_one]
      rw [← hχ, dualEval_apply, dualEval_apply] at h1
      rw [h1]; rfl
    apply hχq
    have : Φ ψ = 1 := by rw [← hχ, hχ1, map_one]; rfl
    exact this
  refine pontryaginDualityStatement_of_bijective_of_isOpenMap ⟨hinj, hsurj⟩ ?_
  exact ((dualEval G).continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ ⟨hinj, hsurj⟩)).isOpenMap

end NumberFieldKB.Pontryagin
