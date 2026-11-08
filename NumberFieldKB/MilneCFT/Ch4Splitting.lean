import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Centralizer

/-!
# Milne, Class Field Theory, Chapter IV, §3: splitting fields

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §3, "Maximal subfields" (continued): splitting fields and maximal subfields
(Cor. 3.6, Cor. 3.7), separable maximal subfields (Prop. 3.8), and
$\mathrm{Br}(k) = \bigcup_L \mathrm{Br}(L/k)$ (Cor. 3.10, and Prop. 2.17 of §2, which is proved here
from Prop. 3.8 and Cor. 3.6 rather than by Milne's descent from the algebraic closure).

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u v

variable {K : Type u} [Field K]

/-! ### Helper lemmas on splitting fields -/

theorem isSplitBy_of_algHom (A : Type u) [Ring A] [Algebra K A] (L M : Type u) [Field L]
    [Field M] [Algebra K L] [Algebra K M] (e : L →ₐ[K] M) (h : IsSplitBy (K := K) L A) :
    IsSplitBy (K := K) M A := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  let _ : Algebra L M := e.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  refine ⟨n, hn, ⟨?_⟩⟩
  exact ((Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M).symm
      AlgEquiv.refl).trans (Algebra.TensorProduct.assoc K L M M L A)).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl f).trans
      ((bcMat (K := L) M n L).trans (AlgEquiv.mapMatrix (Algebra.TensorProduct.rid L M M))))

theorem isSplitBy_of_algEquiv (A A' : Type u) [Ring A] [Algebra K A] [Ring A'] [Algebra K A']
    (L : Type u) [Field L] [Algebra K L] (e : A ≃ₐ[K] A') (h : IsSplitBy (K := K) L A) :
    IsSplitBy (K := K) L A' := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨(Algebra.TensorProduct.congr AlgEquiv.refl e).symm.trans f⟩⟩

theorem isSplitBy_congr_brauer {A B : CSA.{u, u} K} (h : IsBrauerEquivalent A B)
    (L : Type u) [Field L] [Algebra K L] :
    IsSplitBy (K := K) L A ↔ IsSplitBy (K := K) L B := by
  rw [← mk_mem_relBrauer_iff, ← mk_mem_relBrauer_iff, (BrauerGroup.mk_eq_mk_iff A B).2 h]

theorem isSplitBy_op_iff (A : CSA.{u, u} K) (L : Type u) [Field L] [Algebra K L] :
    IsSplitBy (K := K) L A ↔ IsSplitBy (K := K) L (CSA.op A) := by
  rw [← mk_mem_relBrauer_iff, ← mk_mem_relBrauer_iff, ← inv_mem_iff (x := BrauerGroup.mk A),
    BrauerGroup.inv_mk]

theorem split_op_core (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] (ι : L →ₐ[K] A) (mod : Module L A) (hst : IsScalarTower K L A)
    (hsm : ∀ (l : L) (x : A), l • x = ι l * x)
    (hdim : Module.finrank K A = Module.finrank K L ^ 2) :
    IsSplitBy (K := K) L Aᵐᵒᵖ := by
  have : SMulCommClass L K A := ⟨fun l k x => by rw [hsm, hsm, mul_smul_comm]⟩
  have : Module.Finite L A := Module.Finite.of_restrictScalars_finite K L A
  let g : Aᵐᵒᵖ →ₐ[K] Module.End L A :=
    { toFun := fun a =>
        { toFun := fun x => x * a.unop
          map_add' := fun x y => add_mul x y _
          map_smul' := fun l x => by simp only [hsm, RingHom.id_apply, mul_assoc] }
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [mul_assoc]
      map_zero' := by ext x; simp
      map_add' := fun a b => by ext x; simp [mul_add]
      commutes' := fun k => by
        ext x
        simp
        rw [← Algebra.commutes, ← Algebra.smul_def] }
  have hc : ∀ (l : L) (a : Aᵐᵒᵖ), Commute (Algebra.ofId L (Module.End L A) l) (g a) := by
    intro l a
    ext x
    simp [g, hsm, mul_assoc]
  let Φ : L ⊗[K] Aᵐᵒᵖ →ₐ[L] Module.End L A :=
    Algebra.TensorProduct.lift (Algebra.ofId L (Module.End L A)) g hc
  have hinj : Function.Injective Φ := RingHom.injective Φ.toRingHom
  have h1 : Module.finrank L (L ⊗[K] Aᵐᵒᵖ) = Module.finrank K A := by
    rw [Module.finrank_baseChange]
    exact (MulOpposite.opLinearEquiv K).symm.finrank_eq
  have hL : 0 < Module.finrank K L := Module.finrank_pos
  have h2 : Module.finrank K A = Module.finrank K L * Module.finrank L A :=
    (Module.finrank_mul_finrank K L A).symm
  have h3 : Module.finrank L A = Module.finrank K L := by
    rw [hdim, sq] at h2
    exact (Nat.eq_of_mul_eq_mul_left hL h2).symm
  have h4 : Module.finrank L (Module.End L A) = Module.finrank K A := by
    rw [Module.finrank_linearMap, h3, hdim, sq]
  have hbij : Function.Bijective Φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Φ.toLinearMap) (h1.trans h4.symm)).1 hinj⟩
  let e : L ⊗[K] Aᵐᵒᵖ ≃ₐ[L] Module.End L A := AlgEquiv.ofBijective Φ hbij
  refine ⟨Module.finrank L A, ?_, ⟨e.trans (algEquivMatrix (Module.finBasis L A))⟩⟩
  rw [h3]
  exact hL.ne'

theorem split_of_subfield (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (L : Subalgebra K A) (hL : IsField L)
    (hdim : Module.finrank K A = Module.finrank K L ^ 2) :
    letI := hL.toField
    IsSplitBy (K := K) L A := by
  letI := hL.toField
  have : FiniteDimensional K L := inferInstance
  let ι : L →ₐ[K] A := L.val
  let _ : Module L A := Module.compHom A ι.toRingHom
  have : IsScalarTower K L A := ⟨fun k l x => by
    show ι (k • l) * x = k • (ι l * x)
    rw [map_smul, smul_mul_assoc]⟩
  have hop : IsSplitBy (K := K) L Aᵐᵒᵖ :=
    split_op_core A L ι (Module.compHom A ι.toRingHom) this (fun _ _ => rfl) hdim
  let Ac : CSA.{u, u} K := { toAlgCat := AlgCat.of K A }
  exact (isSplitBy_op_iff Ac L).2 hop

/-- Matrices over `L` acting `K`-linearly on `L^m`. -/
noncomputable def matAct (L : Type u) [Field L] [Algebra K L] (m : ℕ) :
    Matrix (Fin m) (Fin m) L →ₐ[K] Module.End K (Fin m → L) where
  toFun M := (Matrix.mulVecLin M).restrictScalars K
  map_one' := by ext v i; simp
  map_mul' M N := by ext v i; simp [Matrix.mulVec_mulVec]
  map_zero' := by ext v i; simp
  map_add' M N := by ext v i; simp [Matrix.add_mulVec]
  commutes' k := by
    ext v i
    simp [Matrix.algebraMap_matrix_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

theorem matAct_apply (L : Type u) [Field L] [Algebra K L] (m : ℕ) (M : Matrix (Fin m) (Fin m) L)
    (v : Fin m → L) : matAct (K := K) L m M v = M.mulVec v := rfl

theorem exists_complement (A : CSA.{u, u} K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : IsSplitBy (K := K) L A) :
    ∃ C : CSA.{u, u} K, BrauerGroup.mk A * BrauerGroup.mk C = 1 ∧ Nonempty (L →ₐ[K] C) ∧
      Module.finrank K C = Module.finrank K L ^ 2 := by
  classical
  obtain ⟨m, hm, ⟨e⟩⟩ := h
  haveI : NeZero m := ⟨hm⟩
  let N := Module.finrank K (Fin m → L)
  let ψ : Module.End K (Fin m → L) ≃ₐ[K] Matrix (Fin N) (Fin N) K :=
    algEquivMatrix (Module.finBasis K (Fin m → L))
  let ρ : A →ₐ[K] Matrix (Fin N) (Fin N) K :=
    ψ.toAlgHom.comp ((matAct L m).comp
      ((e.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight))
  let lam : L →ₐ[K] Matrix (Fin N) (Fin N) K := ψ.toAlgHom.comp (Algebra.lsmul K K (Fin m → L))
  have hNpos : 0 < N := Module.finrank_pos
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hinj : Function.Injective ρ := RingHom.injective ρ.toRingHom
  have hc0 : ∀ (l : L) (M : Matrix (Fin m) (Fin m) L),
      Commute (Algebra.lsmul K K (Fin m → L) l) (matAct (K := K) L m M) := by
    intro l M
    ext v i
    simp [matAct_apply, Algebra.lsmul_apply, Matrix.mulVec_smul]
  have hcomm : ∀ (l : L) (a : A), Commute (lam l) (ρ a) := fun l a => (hc0 l _).map ψ
  let eB : A ≃ₐ[K] ρ.range := AlgEquiv.ofInjective ρ hinj
  haveI : IsSimpleRing ρ.range := IsSimpleRing.of_ringEquiv eB.toRingEquiv inferInstance
  haveI : Algebra.IsCentral K ρ.range := Algebra.IsCentral.of_algEquiv K A ρ.range eB
  obtain ⟨hC1, hC2⟩ := cor_3_3 (K := K) (Matrix (Fin N) (Fin N) K) ρ.range
  obtain ⟨hS, -, hdimEq⟩ := thm_3_1 (K := K) (Matrix (Fin N) (Fin N) K) ρ.range
  haveI := hC1
  haveI := hS
  let C := Subalgebra.centralizer K (ρ.range : Set (Matrix (Fin N) (Fin N) K))
  let Cc : CSA.{u, u} K := { toAlgCat := AlgCat.of K C }
  let lam' : L →ₐ[K] C := lam.codRestrict C (fun l => by
    rw [Subalgebra.mem_centralizer_iff]
    rintro x ⟨a, rfl⟩
    exact (hcomm l a).eq.symm)
  have hdimA : Module.finrank K A = m * m := by
    rw [← Module.finrank_baseChange (R := L) (S := K) (M' := A), e.toLinearEquiv.finrank_eq]
    rw [Module.finrank_matrix]
    simp
  have hN : N = m * Module.finrank K L := by
    simp [N, Module.finrank_pi_fintype]
  refine ⟨Cc, ?_, ⟨lam'⟩, ?_⟩
  · rw [BrauerGroup.mk_mul_mk, BrauerGroup.mk_eq_one_iff]
    exact ⟨N, hNpos.ne', ⟨(Algebra.TensorProduct.congr eB AlgEquiv.refl).trans
      (AlgEquiv.ofBijective _ hC2)⟩⟩
  · have h1 : Module.finrank K ρ.range = m * m := by
      rw [← hdimA]
      exact eB.toLinearEquiv.finrank_eq.symm
    have h2 : Module.finrank K (Matrix (Fin N) (Fin N) K) = N * N := by
      rw [Module.finrank_matrix]
      simp
    rw [h1, h2] at hdimEq
    have hm2 : 0 < m * m := Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hm)
    show Module.finrank K C = _
    apply Nat.eq_of_mul_eq_mul_left hm2
    rw [hdimEq, hN]
    ring

/-! ### Helper lemmas for Proposition 3.8 -/

theorem inv_mem_of_finite {D : Type v} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (S : Subalgebra K D) {a : D} (ha : a ∈ S) (h0 : a ≠ 0) : a⁻¹ ∈ S := by
  let f : S →ₗ[K] S := LinearMap.mulLeft K (⟨a, ha⟩ : S)
  have hinj : Function.Injective f := fun u v h => by
    have : a * (u : D) = a * v := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ h0 this)
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  have h1 : a * (b : D) = 1 := congrArg Subtype.val hb
  rw [inv_eq_of_mul_eq_one_right h1]
  exact b.2

/-- Adjoining to a separable subfield `ι F` an element `x` commuting with it and a root of a
separable polynomial over `F` gives a subfield of `D` whose elements are all separable over `K`. -/
theorem exists_sep_ext {D : Type v} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (F : Type v) [Field F] [Algebra K F] [Algebra.IsSeparable K F] (ι : F →ₐ[K] D) (x : D)
    (hxc : ∀ f : F, ι f * x = x * ι f) (p : Polynomial F) (hp : p.Separable)
    (hx : p.eval₂ (ι : F →+* D) x = 0) :
    ∃ L' : Subalgebra K D, IsField L' ∧ (∀ y ∈ L', IsSeparable K y) ∧
      ι.range ≤ L' ∧ x ∈ L' := by
  classical
  let s : Set D := insert x (Set.range ι)
  let L' : Subalgebra K D := Algebra.adjoin K s
  have hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro a (rfl | ⟨f, rfl⟩) b (rfl | ⟨g, rfl⟩)
    · rfl
    · exact (hxc g).symm
    · exact hxc f
    · rw [← map_mul, ← map_mul, mul_comm]
  have hcomm : ∀ a ∈ L', ∀ b ∈ L', a * b = b * a := by
    intro a ha b hb
    have h1 : ∀ c ∈ s, Commute c a := fun c hc =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (fun b' hb' => hs c hc b' hb')
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb
      (fun c hc => (h1 c hc).symm)).eq
  have hfield : IsField L' :=
    { exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2)
      mul_inv_cancel := fun {a} ha =>
        ⟨⟨(a : D)⁻¹, inv_mem_of_finite L' a.2 (fun h => ha (Subtype.ext h))⟩,
          Subtype.ext (mul_inv_cancel₀ (fun h => ha (Subtype.ext h)))⟩ }
  have hxL : x ∈ L' := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hιL : ∀ f : F, ι f ∈ L' := fun f => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨f, rfl⟩)
  refine ⟨L', hfield, ?_, fun d ⟨f, hf⟩ => hf ▸ hιL f, hxL⟩
  letI := hfield.toField
  let j : F →ₐ[K] L' := ι.codRestrict L' hιL
  have hjinj : Function.Injective j := (j : F →+* L').injective
  letI : Algebra F L' := j.toRingHom.toAlgebra
  haveI : IsScalarTower K F L' := IsScalarTower.of_algebraMap_eq fun k => (j.commutes k).symm
  let x' : L' := ⟨x, hxL⟩
  have hsepx : IsSeparable F x' := by
    have h0 : Polynomial.aeval x' p = 0 := by
      apply L'.val.injective
      have := Polynomial.hom_eval₂ p (algebraMap F L') (L'.val : L' →+* D) x'
      rw [map_zero]
      refine Eq.trans ?_ hx
      exact this
    exact hp.of_dvd (minpoly.dvd F x' h0)
  have hsepxK : IsSeparable K x' := IsSeparable.of_algebra_isSeparable_of_isSeparable K hsepx
  have key : ∀ (y : D) (hy : y ∈ L'), (⟨y, hy⟩ : L') ∈ separableClosure K L' := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | ⟨f, rfl⟩
      · exact mem_separableClosure_iff.2 hsepxK
      · refine mem_separableClosure_iff.2 ?_
        show IsSeparable K (j f)
        unfold IsSeparable
        rw [minpoly.algHom_eq j hjinj f]
        exact Algebra.IsSeparable.isSeparable K f
    | algebraMap r => exact (separableClosure K L').algebraMap_mem r
    | add y z hy hz hy' hz' => exact (separableClosure K L').add_mem (x := ⟨y, hy⟩) (y := ⟨z, hz⟩) hy' hz'
    | mul y z hy hz hy' hz' => exact (separableClosure K L').mul_mem (x := ⟨y, hy⟩) (y := ⟨z, hz⟩) hy' hz'
  intro y hy
  have := mem_separableClosure_iff.1 (key y hy)
  unfold IsSeparable at this ⊢
  rwa [← minpoly.algHom_eq L'.val Subtype.val_injective ⟨y, hy⟩] at this

/-- If `L` is a subfield of the central division algebra `D`, separable over `K` and maximal with
this property, then `L` is its own centralizer (Jacobson-Noether). -/
theorem centralizer_le_of_maximal_sep (D : Type v) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] (L : Subalgebra K D) (hL : IsField L)
    (hsepL : ∀ y ∈ L, IsSeparable K y)
    (hmax : ∀ L' : Subalgebra K D, IsField L' → (∀ y ∈ L', IsSeparable K y) → L ≤ L' →
      L' = L) :
    Subalgebra.centralizer K (L : Set D) ≤ L := by
  classical
  by_contra hnot
  obtain ⟨c, hcC, hcL⟩ := SetLike.not_le_iff_exists.1 hnot
  letI := hL.toField
  haveI : IsSimpleRing L := inferInstance
  have hLC : L ≤ Subalgebra.centralizer K (L : Set D) := fun a ha =>
    (Subalgebra.mem_centralizer_iff K).2 fun g hg => congrArg Subtype.val (hL.mul_comm ⟨g, hg⟩ ⟨a, ha⟩)
  letI : DivisionRing (Subalgebra.centralizer K (L : Set D)) :=
    DivisionRing.ofIsUnitOrEqZero fun a => by
      by_cases h : a = 0
      · exact Or.inr h
      · left
        have ha : (a : D) ≠ 0 := fun h' => h (Subtype.ext h')
        refine isUnit_iff_exists.2 ⟨⟨(a : D)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ ha),
          Subtype.ext (inv_mul_cancel₀ ha)⟩
        rw [Subalgebra.mem_centralizer_iff]
        intro g hg
        have h1 : Commute g (a : D) := (Subalgebra.mem_centralizer_iff K).1 a.2 g hg
        exact (h1.inv_right₀).eq
  letI : Algebra L (Subalgebra.centralizer K (L : Set D)) :=
    RingHom.toAlgebra' (Subalgebra.inclusion hLC).toRingHom (fun a b =>
      Subtype.ext ((Subalgebra.mem_centralizer_iff K).1 b.2 a a.2))
  haveI : IsScalarTower K L (Subalgebra.centralizer K (L : Set D)) :=
    IsScalarTower.of_algebraMap_eq fun k => rfl
  haveI : Module.Finite L (Subalgebra.centralizer K (L : Set D)) :=
    Module.Finite.of_restrictScalars_finite K L _
  haveI : Algebra.IsAlgebraic L (Subalgebra.centralizer K (L : Set D)) :=
    Algebra.IsAlgebraic.of_finite L _
  haveI : Algebra.IsCentral L (Subalgebra.centralizer K (L : Set D)) := by
    refine ⟨fun z hz => ?_⟩
    rw [Subalgebra.mem_center_iff] at hz
    have hzD : (z : D) ∈ Subalgebra.centralizer K
        (Subalgebra.centralizer K (L : Set D) : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (hz ⟨g, hg⟩)
    have h2 := (thm_3_1 (K := K) D L).2.1
    rw [h2] at hzD
    exact Algebra.mem_bot.2 ⟨⟨(z : D), hzD⟩, rfl⟩
  have hneq : (⊥ : Subalgebra L (Subalgebra.centralizer K (L : Set D))) ≠ ⊤ := by
    intro hbt
    have h1 : (⟨c, hcC⟩ : Subalgebra.centralizer K (L : Set D)) ∈
        (⊤ : Subalgebra L (Subalgebra.centralizer K (L : Set D))) := trivial
    rw [← hbt, Algebra.mem_bot] at h1
    obtain ⟨l, hl⟩ := h1
    have hlc : (l : D) = c := congrArg Subtype.val hl
    exact hcL (hlc ▸ l.2)
  obtain ⟨y, hy, hysep⟩ := JacobsonNoether.exists_separable_and_not_isCentral'
    (L := L) (D := Subalgebra.centralizer K (L : Set D)) hneq
  haveI : Algebra.IsSeparable K L := ⟨fun y => by
    unfold IsSeparable
    rw [← minpoly.algHom_eq L.val Subtype.val_injective y]
    exact hsepL y y.2⟩
  have hx := Polynomial.hom_eval₂ (minpoly L y) (algebraMap L (Subalgebra.centralizer K (L : Set D)))
    ((Subalgebra.centralizer K (L : Set D)).val : _ →+* D) y
  have hx0 : (minpoly L y).eval₂ (L.val : L →+* D) (y : D) = 0 := by
    have h0 : Polynomial.aeval y (minpoly L y) = 0 := minpoly.aeval L y
    rw [Polynomial.aeval_def] at h0
    rw [h0, map_zero] at hx
    exact hx.symm
  obtain ⟨L', hL', hL'sep, hLL', hyL'⟩ := exists_sep_ext (K := K) L L.val (y : D)
    (fun f => (Subalgebra.mem_centralizer_iff K).1 y.2 f f.2) (minpoly L y) hysep hx0
  have hLL'' : L ≤ L' := by rwa [Subalgebra.range_val] at hLL'
  have heq := hmax L' hL' hL'sep hLL''
  exact hy (Algebra.mem_bot.2 ⟨⟨(y : D), heq ▸ hyL'⟩, rfl⟩)

/-- Corollary 3.6 of Milne: a field $L$ of finite degree over $K$ splits the central simple
$K$-algebra $A$ if and only if some central simple algebra $B$ similar to $A$ contains $L$
(a $K$-algebra embedding $L \to B$) and $[B : K] = [L : K]^2$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.6, p. 133"]
theorem cor_3_6 (A : CSA.{u, u} K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    IsSplitBy (K := K) L A ↔
      ∃ B : CSA.{u, u} K, IsBrauerEquivalent A B ∧ Nonempty (L →ₐ[K] B) ∧
        Module.finrank K B = Module.finrank K L ^ 2 := by
  constructor
  · intro h
    have hop : IsSplitBy (K := K) L (CSA.op A) := (isSplitBy_op_iff A L).1 h
    obtain ⟨C, hmul, ⟨φ⟩, hdim⟩ := exists_complement (CSA.op A) L hop
    refine ⟨C, ?_, ⟨φ⟩, hdim⟩
    rw [← BrauerGroup.mk_eq_mk_iff]
    rw [← BrauerGroup.inv_mk] at hmul
    exact inv_mul_eq_one.1 hmul
  · rintro ⟨B, hAB, ⟨φ⟩, hdim⟩
    have hinj : Function.Injective φ := RingHom.injective φ.toRingHom
    let eR : L ≃ₐ[K] φ.range := AlgEquiv.ofInjective φ hinj
    have hR : IsField φ.range := eR.symm.toMulEquiv.isField (Field.toIsField L)
    have hdimR : Module.finrank K B = Module.finrank K φ.range ^ 2 := by
      rw [hdim, eR.toLinearEquiv.finrank_eq]
    letI := hR.toField
    have hsplit : IsSplitBy (K := K) φ.range B := split_of_subfield B φ.range hR hdimR
    have hLB : IsSplitBy (K := K) L B := isSplitBy_of_algHom B φ.range L eR.symm.toAlgHom hsplit
    exact (isSplitBy_congr_brauer hAB L).2 hLB

/-- Corollary 3.6 of Milne, "in particular": every subfield $L$ of $A$ with
$[L : K]^2 = [A : K]$ splits $A$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.6 (in particular), p. 133"]
theorem cor_3_6_subfield (A : Type u) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (L : Subalgebra K A) (hL : IsField L)
    (hdim : Module.finrank K A = Module.finrank K L ^ 2) :
    letI := hL.toField
    IsSplitBy (K := K) L A :=
  split_of_subfield A L hL hdim

/-- Corollary 3.7 of Milne: let $D$ be a central division algebra of degree $n^2$ over $K$ and
$L$ a field of degree $n$ over $K$.  Then $L$ splits $D$ if and only if $L$ embeds in $D$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.7, p. 134"]
theorem cor_3_7 (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (L : Type u) [Field L] [Algebra K L] {n : ℕ}
    (hD : Module.finrank K D = n ^ 2) (hL : Module.finrank K L = n) :
    IsSplitBy (K := K) L D ↔ Nonempty (L →ₐ[K] D) := by
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      have := Module.finrank_pos (R := K) (M := D)
      rw [hD, h0] at this
      simp at this
    · exact h0
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (hL ▸ hnpos)
  let Dc : CSA.{u, u} K := { toAlgCat := AlgCat.of K D }
  constructor
  · intro h
    obtain ⟨B, hDB, ⟨φ⟩, hdim⟩ := (cor_3_6 Dc L).1 h
    have : IsArtinianRing B := IsArtinianRing.of_finite K B
    obtain ⟨r, hr, D', _, _, _, ⟨f⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
    obtain ⟨g⟩ := remark_2_13a_matrix Dc B hDB D D' one_ne_zero hr.out
      (BrauerGroup.matOne D).symm f
    have hdimD' : Module.finrank K D' = n ^ 2 := by
      rw [← hD]
      exact g.symm.toLinearEquiv.finrank_eq
    have h1 : Module.finrank K B = r * r * Module.finrank K D' := by
      rw [f.toLinearEquiv.finrank_eq, Module.finrank_matrix]
      simp
    have hr1 : r = 1 := by
      rw [hdim, hL, hdimD'] at h1
      have hn2 : 0 < n ^ 2 := by positivity
      have h2 : r * r = 1 := Nat.eq_of_mul_eq_mul_right hn2 (by linarith)
      exact Nat.eq_one_of_mul_eq_one_right h2
    subst hr1
    exact ⟨((f.trans ((BrauerGroup.matOne D').trans g.symm)).toAlgHom).comp φ⟩
  · rintro ⟨φ⟩
    refine (cor_3_6 Dc L).2 ⟨Dc, isBrauerEquivalent_of_algEquiv AlgEquiv.refl, ⟨φ⟩, ?_⟩
    show Module.finrank K D = _
    rw [hD, hL]

/-- Proposition 3.8 of Milne: every central division algebra over $K$ contains a maximal
subfield separable over $K$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 3.8, p. 134"]
theorem prop_3_8 (D : Type v) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] :
    ∃ (L : Subalgebra K D) (hL : IsField L),
      (∀ L' : Subalgebra K D, IsField L' → L ≤ L' → L' = L) ∧
        Algebra.IsSeparable K L := by
  classical
  let P : Subalgebra K D → Prop := fun L => IsField L ∧ ∀ y ∈ L, IsSeparable K y
  have hP0 : P ⊥ := by
    refine ⟨(Algebra.botEquiv K D).toMulEquiv.isField (Field.toIsField K), ?_⟩
    intro y hy
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.1 hy
    exact isSeparable_algebraMap k
  have hbd : ∀ L : Subalgebra K D, Module.finrank K L ≤ Module.finrank K D := fun L =>
    LinearMap.finrank_le_finrank_of_injective (f := L.val.toLinearMap) Subtype.val_injective
  obtain ⟨L, hLP, hLmax⟩ : ∃ L, P L ∧ ∀ L', P L' → Module.finrank K L' ≤ Module.finrank K L := by
    let S : Set ℕ := {n | ∃ L, P L ∧ Module.finrank K L = n}
    have hne : S.Nonempty := ⟨_, ⊥, hP0, rfl⟩
    have hbdd : BddAbove S := ⟨Module.finrank K D, by rintro n ⟨L, -, rfl⟩; exact hbd L⟩
    obtain ⟨L, hL, hLn⟩ := Nat.sSup_mem hne hbdd
    exact ⟨L, hL, fun L' hL' => hLn ▸ le_csSup hbdd ⟨L', hL', rfl⟩⟩
  obtain ⟨hL, hLsep⟩ := hLP
  have hmax : ∀ L' : Subalgebra K D, IsField L' → (∀ y ∈ L', IsSeparable K y) → L ≤ L' →
      L' = L := by
    intro L' hL' hs hle
    exact (Subalgebra.eq_of_le_of_finrank_le hle (hLmax L' ⟨hL', hs⟩)).symm
  have hC := centralizer_le_of_maximal_sep D L hL hLsep hmax
  have hLC : L ≤ Subalgebra.centralizer K (L : Set D) := fun a ha =>
    (Subalgebra.mem_centralizer_iff K).2 fun g hg =>
      congrArg Subtype.val (hL.mul_comm ⟨g, hg⟩ ⟨a, ha⟩)
  have hCeq : Subalgebra.centralizer K (L : Set D) = L := le_antisymm hC hLC
  refine ⟨L, hL, ?_, ⟨fun y => ?_⟩⟩
  · intro L' hL' hle
    have := ((cor_3_4 (K := K) D L hL).out 1 3).1 hCeq
    exact this L' hle (fun a ha b hb => congrArg Subtype.val (hL'.mul_comm ⟨a, ha⟩ ⟨b, hb⟩))
  · unfold IsSeparable
    rw [← minpoly.algHom_eq L.val Subtype.val_injective y]
    exact hLsep y y.2

theorem exists_sep_split (x : BrauerGroup.{u, u} K) :
    ∃ (D : CSA.{u, u} K) (L : Type u) (_ : Field L) (_ : Algebra K L),
      BrauerGroup.mk D = x ∧ FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        IsSplitBy (K := K) L D := by
  obtain ⟨D, hD, rfl⟩ := remark_2_13a_exists x
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  obtain ⟨L, hL, hmax, hsep⟩ := prop_3_8 (K := K) (D : Type u)
  have hdim := (cor_3_5 (K := K) (D : Type u) L hL).1 hmax
  letI := hL.toField
  exact ⟨D, L, inferInstance, inferInstance, rfl, inferInstance, hsep,
    split_of_subfield (D : Type u) L hL hdim⟩

/-- Corollary 3.10 of Milne: $\mathrm{Br}(K) = \bigcup \mathrm{Br}(L/K)$, $L$ running over the
finite Galois extensions of $K$ in a fixed separable closure. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.10, p. 134"]
theorem cor_3_10 (x : BrauerGroup.{u, u} K) :
    ∃ L : IntermediateField K (SeparableClosure K), FiniteDimensional K L ∧ IsGalois K L ∧
      x ∈ relBrauer K L := by
  obtain ⟨D, L, _, _, rfl, hfin, hsep, hsplit⟩ := exists_sep_split x
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let M0 : IntermediateField K (SeparableClosure K) := ι.fieldRange
  let e : L ≃ₐ[K] M0 := AlgEquiv.ofInjectiveField ι
  haveI : FiniteDimensional K M0 := e.toLinearEquiv.finiteDimensional
  haveI : Algebra.IsSeparable K M0 := inferInstance
  refine ⟨IntermediateField.normalClosure K M0 (SeparableClosure K), inferInstance, inferInstance, ?_⟩
  rw [mk_mem_relBrauer_iff]
  exact isSplitBy_of_algHom D L _
    ((IntermediateField.inclusion (IntermediateField.le_normalClosure M0)).comp e.toAlgHom)
    hsplit

/-- Proposition 2.17 of Milne (proved here from Prop. 3.8 and Cor. 3.6, not by Milne's descent from the algebraic closure): $\mathrm{Br}(K) = \bigcup \mathrm{Br}(L/K)$, $L$ running over the
finite extensions of $K$ in a fixed algebraic closure; that is, every central simple algebra over
$K$ is split by a finite extension of $K$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 2.17, p. 131"]
theorem prop_2_17 (x : BrauerGroup.{u, u} K) :
    ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
      x ∈ relBrauer K L := by
  obtain ⟨D, L, _, _, rfl, hfin, hsep, hsplit⟩ := exists_sep_split x
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let M0 : IntermediateField K (AlgebraicClosure K) := ι.fieldRange
  let e : L ≃ₐ[K] M0 := AlgEquiv.ofInjectiveField ι
  haveI : FiniteDimensional K M0 := e.toLinearEquiv.finiteDimensional
  refine ⟨M0, inferInstance, ?_⟩
  rw [mk_mem_relBrauer_iff]
  exact isSplitBy_of_algHom D L _ e.toAlgHom hsplit

end NumberFieldKB.MilneCFT.Ch4
