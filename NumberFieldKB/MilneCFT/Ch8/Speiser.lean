import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import QuadFormsKB.Citation
import Mathlib.Control.Traversable.Equiv

/-!
# Speiser's Hilbert 90 for $\mathrm{GL}_n$ (for Milne, *Class Field Theory*, VIII, Remark 6.4)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §6,
Remark 6.4 (pdf p. 261, printed p. 252), which reads Theorem 6.3 (Hasse–Minkowski) as the injectivity of
$H^1(K, O) \to \prod_v H^1(K_v, O)$. The first input of that reading is Speiser's generalization of Hilbert's
Theorem 90: for a finite Galois extension $L/K$ with group $G$, $H^1(G, \mathrm{GL}_n(L)) = 1$ (Serre, *Local Fields*,
Ch. X, §1, Prop. 3; Speiser 1919).

## What is formalized

* `speiser_hilbert90`: for a finite-dimensional field extension $L/K$ (Galois or not; $G = \operatorname{Aut}_K(L)$)
  and an index type $\iota$ (Milne's $n$ variables), every crossed homomorphism
  $a : G \to \mathrm{GL}_\iota(L)$, $a(\sigma\tau) = a(\sigma)\,\sigma(a(\tau))$, is a coboundary:
  $a(\sigma) = B\,\sigma(B)^{-1}$ for some $B \in \mathrm{GL}_\iota(L)$.

*Proof* (Serre's, with Dedekind's independence of characters in place of the infinite-field argument). For
$v \in L^\iota$ put $b(v) = \sum_{\sigma} a(\sigma)\,\sigma(v)$. The $b(v)$ span $L^\iota$: otherwise a nonzero
$L$-linear form $f$ kills all $b(xv)$, $x \in L$, i.e. $\sum_\sigma \sigma(x)\, f(a(\sigma)\sigma(v)) = 0$ for all $x$;
by Dedekind (`linearIndependent_monoidHom`) every coefficient vanishes, and the one at $\sigma = 1$ is $f(v)$.
Choose $v_1, \dots, v_n$ with $b(v_i)$ a basis and let $C$ have columns $v_i$; then $B = \sum_\sigma a(\sigma)\sigma(C)$
is invertible and $a(\tau)\,\tau(B) = \sum_\sigma a(\tau\sigma)\,(\tau\sigma)(C) = B$.
-/

open Matrix

namespace NumberFieldKB.MilneCFT.Ch8

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The action of $\sigma \in \operatorname{Aut}_K(L)$ on $\mathrm{GL}_\iota(L)$, entrywise. -/
abbrev galGL (σ : L ≃ₐ[K] L) : GL ι L →* GL ι L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

/-- A crossed homomorphism (1-cocycle) $a : \operatorname{Aut}_K(L) \to \mathrm{GL}_\iota(L)$:
$a(\sigma\tau) = a(\sigma)\,\sigma(a(\tau))$. -/
def IsGLCocycle (a : (L ≃ₐ[K] L) → GL ι L) : Prop :=
  ∀ σ τ, a (σ * τ) = a σ * galGL σ (a τ)

omit [FiniteDimensional K L] in
theorem IsGLCocycle.map_one {a : (L ≃ₐ[K] L) → GL ι L} (ha : IsGLCocycle a) : a 1 = 1 := by
  have h := ha 1 1
  rw [mul_one] at h
  have h1 : galGL (ι := ι) (1 : L ≃ₐ[K] L) (a 1) = a 1 := by
    ext i j
    rfl
  rw [h1] at h
  exact (mul_eq_left.mp h.symm)

/-- **Speiser's Hilbert 90 for $\mathrm{GL}_n$** (Serre, *Local Fields*, X, §1, Prop. 3; used in Milne, *CFT*,
VIII, Remark 6.4, p. 252): for a finite-dimensional extension $L/K$, every crossed homomorphism
$\operatorname{Aut}_K(L) \to \mathrm{GL}_\iota(L)$ is a coboundary, $a(\sigma) = B\,\sigma(B)^{-1}$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Remark 6.4, p. 252 (Hilbert 90 for GL_n, input)"]
theorem speiser_hilbert90 (a : (L ≃ₐ[K] L) → GL ι L) (ha : IsGLCocycle a) :
    ∃ B : GL ι L, ∀ σ, a σ = B * (galGL σ B)⁻¹ := by
  classical
  -- the twisted trace on vectors
  let b : (ι → L) → (ι → L) := fun v => ∑ σ : L ≃ₐ[K] L, (a σ : Matrix ι ι L) *ᵥ (fun i => σ (v i))
  -- the `b v` span everything
  have hspan : Submodule.span L (Set.range b) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
      (Module.Projective.of_free)
    apply hf0
    have hfb : ∀ v, f (b v) = 0 := by
      intro v
      have : f (b v) ∈ (Submodule.span L (Set.range b)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨v, rfl⟩)
      rw [hf] at this
      exact this
    -- Dedekind: the characters `σ` are linearly independent
    have hli : LinearIndependent L (fun σ : L ≃ₐ[K] L => ((σ : L →* L) : L → L)) :=
      (linearIndependent_monoidHom L L).comp (fun σ : L ≃ₐ[K] L => (σ : L →* L))
        (fun σ τ h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)
    have hcoef : ∀ v : ι → L, ∀ σ : L ≃ₐ[K] L, f ((a σ : Matrix ι ι L) *ᵥ (fun i => σ (v i))) = 0 := by
      intro v
      have hsum : ∑ σ : L ≃ₐ[K] L,
          f ((a σ : Matrix ι ι L) *ᵥ (fun i => σ (v i))) • ((σ : L →* L) : L → L) = 0 := by
        funext x
        have := hfb (x • v)
        simp only [b, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
        rw [← this]
        refine Finset.sum_congr rfl fun σ _ => ?_
        have : (fun i => σ (x * v i)) = σ x • (fun i => σ (v i)) := by
          funext i; simp [map_mul]
        rw [this, Matrix.mulVec_smul, map_smul, smul_eq_mul, mul_comm]
        rfl
      exact fun σ => (Fintype.linearIndependent_iff.mp hli) _ hsum σ
    refine LinearMap.ext fun v => ?_
    have := hcoef v 1
    rw [ha.map_one] at this
    simpa using this
  -- pick a basis among the `b v`
  obtain ⟨s, hs, hsspan, hsli⟩ := exists_linearIndependent L (Set.range b)
  rw [hspan] at hsspan
  let β := Module.Basis.mk hsli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hsspan])
  have hcard : Fintype.card ι = Module.finrank L (ι → L) := by simp
  let _ : Fintype s := hsli.setFinite.fintype
  let e : ι ≃ s := Fintype.equivOfCardEq (by rw [hcard, Module.finrank_eq_card_basis β])
  have hv : ∀ i, ∃ v, b v = (e i : ι → L) := fun i => hs (e i).2
  choose v hv using hv
  -- the matrix `C` with columns `v i`, and `B = ∑ a σ σ(C)`
  let C : Matrix ι ι L := Matrix.of fun i j => v j i
  let Bm : Matrix ι ι L := ∑ σ : L ≃ₐ[K] L, (a σ : Matrix ι ι L) * C.map σ
  have hBcol : ∀ j, (fun i => Bm i j) = b (v j) := by
    intro j
    funext i
    simp only [Bm, b, C, Matrix.sum_apply, Finset.sum_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.map_apply, Matrix.of_apply]
  have hBunit : IsUnit Bm := by
    rw [← Matrix.linearIndependent_col_iff_isUnit]
    have : Bm.col = fun j => (e j : ι → L) := by
      funext j
      rw [← hv j, ← hBcol j]
      rfl
    rw [this]
    exact hsli.comp _ e.injective
  let B : GL ι L := hBunit.unit
  have hB : (B : Matrix ι ι L) = Bm := rfl
  refine ⟨B, fun τ => ?_⟩
  -- `a τ * τ(B) = B`
  have key : (a τ : Matrix ι ι L) * Bm.map τ = Bm := by
    change (a τ : Matrix ι ι L) * (RingHom.mapMatrix (τ : L →+* L)) Bm = Bm
    simp only [Bm]
    rw [map_sum, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_)
    have hc := congrArg (fun g : GL ι L => (g : Matrix ι ι L)) (ha τ σ)
    simp only [Units.val_mul] at hc
    rw [map_mul, ← Matrix.mul_assoc, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map,
      Equiv.coe_mulLeft, hc]
    rfl
  have key' : a τ * galGL τ B = B := by
    ext1
    rw [Units.val_mul, hB]
    exact key
  exact eq_mul_inv_of_mul_eq key'

end NumberFieldKB.MilneCFT.Ch8
