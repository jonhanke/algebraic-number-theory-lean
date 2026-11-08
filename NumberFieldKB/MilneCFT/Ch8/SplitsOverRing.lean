import NumberFieldKB.MilneCFT.Ch8.RelativeBrauer

/-!
# Splitting of central simple algebras over commutative algebras

Helpers for `Ch8.LocalRelBrOrder` and `Ch8.RelativeHasse`: `SplitsOverRing R A` (that is,
$R\otimes_FA\cong M_n(R)$) is inherited along algebra maps $R\to S$, is invariant under isomorphisms of $R$, and holds
over a finite product of fields when it holds over each factor. Over a field it says that the base change of $[A]$ is
trivial. Also: the $n$-torsion of $\mathbb Q/\mathbb Z$ has exactly $n$ elements.
-/

open TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

open Ch4

variable {F : Type} [Field F]

/-- `bcMatKR` over a commutative ring `k`. -/
noncomputable def bcMatKC {k : Type} [CommRing k] (M : Type) [CommRing M] [Algebra k M] (n : ℕ)
    (A : Type) [Ring A] [Algebra k A] :
    M ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin n) (Fin n) (M ⊗[k] A) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor (Fin n) k A)).trans
    ((Algebra.TensorProduct.assoc k k k M A (Matrix (Fin n) (Fin n) k)).symm.trans
      (matrixEquivTensor (Fin n) k (M ⊗[k] A)).symm)

/-- `bcMatR` over a commutative ring `k`. -/
noncomputable def bcMatC {k : Type} [CommRing k] (M : Type) [CommRing M] [Algebra k M] (n : ℕ)
    (A : Type) [Ring A] [Algebra k A] :
    M ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[M] Matrix (Fin n) (Fin n) (M ⊗[k] A) :=
  AlgEquiv.ofRingEquiv (f := (bcMatKC M n A).toRingEquiv) fun l => by
    have h1 : algebraMap M (M ⊗[k] Matrix (Fin n) (Fin n) A) l = l ⊗ₜ[k] 1 := rfl
    show bcMatKC M n A (algebraMap M _ l) = _
    rw [h1]
    have h2 : bcMatKC M n A (l ⊗ₜ[k] 1) = (matrixEquivTensor (Fin n) k (M ⊗[k] A)).symm
        ((l ⊗ₜ[k] (1 : A)) ⊗ₜ[k] (1 : Matrix (Fin n) (Fin n) k)) := by
      simp only [bcMatKC, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, map_one]
      rw [Algebra.TensorProduct.one_def (A := A), Algebra.TensorProduct.assoc_symm_tmul]
      rfl
    rw [h2, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.smul_one_eq_diagonal, Matrix.algebraMap_eq_diagonal]
    rfl

/-- A splitting over `R` gives a splitting over every commutative `R`-algebra (through `φ : R →ₐ[F] S`). -/
theorem SplitsOverRing.of_algHom {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) {A : CSA.{0, 0} F} (h : SplitsOverRing R A) : SplitsOverRing S A := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  refine ⟨n, hn, ?_⟩
  let _ : Algebra R S := φ.toRingHom.toAlgebra
  have : IsScalarTower F R S := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact ⟨((Algebra.TensorProduct.congr (Algebra.TensorProduct.rid R S S).symm
      AlgEquiv.refl).trans (Algebra.TensorProduct.assoc F R S S R A)).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl f).trans
      ((bcMatC (k := R) S n R).trans (AlgEquiv.mapMatrix (Algebra.TensorProduct.rid R S S))))⟩

/-- `SplitsOverRing` is invariant under isomorphisms of the commutative algebra. -/
theorem SplitsOverRing.congr {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (e : R ≃ₐ[F] S) (A : CSA.{0, 0} F) : SplitsOverRing R A ↔ SplitsOverRing S A :=
  ⟨SplitsOverRing.of_algHom e.toAlgHom, SplitsOverRing.of_algHom e.symm.toAlgHom⟩

/-- Over a field, `SplitsOverRing` is splitting: the base change of the class is trivial. -/
theorem splitsOverRing_field_iff (M : Type) [Field M] [Algebra F M] (A : CSA.{0, 0} F) :
    SplitsOverRing M A ↔ baseChange M (BrauerGroup.mk A) = 1 := by
  rw [← MonoidHom.mem_ker, ← relBrauer, mk_mem_relBrauer_iff]
  rfl

/-- **Splitting over a finite product of fields**: a central simple algebra split by each factor is split by the
product. -/
theorem splitsOverRing_pi {ι : Type} [Fintype ι] [Nonempty ι] (M : ι → Type) [∀ i, Field (M i)]
    [∀ i, Algebra F (M i)] (A : CSA.{0, 0} F) (h : ∀ i, SplitsOverRing (M i) A) :
    SplitsOverRing (∀ i, M i) A := by
  classical
  choose n hn f using fun i => h i
  have hf : ∀ i, M i ⊗[F] A ≃ₐ[M i] Matrix (Fin (n i)) (Fin (n i)) (M i) := fun i => (f i).some
  have hsq : ∀ i, n i * n i = Module.finrank F A := by
    intro i
    have h1 := LinearEquiv.finrank_eq (hf i).toLinearEquiv
    rw [Module.finrank_baseChange, Module.finrank_matrix] at h1
    simpa using h1.symm
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hall : ∀ i, n i = n i0 := fun i => Nat.mul_self_inj.1 ((hsq i).trans (hsq i0).symm)
  let e1 : (∀ i, M i) ⊗[F] A ≃ₐ[F] ∀ i, Matrix (Fin (n i0)) (Fin (n i0)) (M i) :=
    ((Algebra.TensorProduct.comm F (∀ i, M i) A).trans
      ((Algebra.TensorProduct.piRight F F A M).trans
        (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F A (M i)))).trans
      (AlgEquiv.piCongrRight fun i =>
        ((hf i).restrictScalars F).trans
          (Matrix.reindexAlgEquiv F (M i) (finCongr (hall i))))
  let e2 : (∀ i, M i) ⊗[F] A ≃ₐ[F] Matrix (Fin (n i0)) (Fin (n i0)) (∀ i, M i) :=
    e1.trans (Matrix.piAlgEquiv (β := M) (n := Fin (n i0)) F).symm
  refine ⟨n i0, hn i0, ⟨AlgEquiv.ofRingEquiv (f := e2.toRingEquiv) fun r => ?_⟩⟩
  have h1 : algebraMap (∀ i, M i) ((∀ i, M i) ⊗[F] A) r = r ⊗ₜ[F] (1 : A) := rfl
  show e2 (algebraMap _ _ r) = _
  rw [h1]
  apply (Matrix.piAlgEquiv (β := M) (n := Fin (n i0)) F).injective
  have h3 : e2 (r ⊗ₜ[F] (1 : A)) = (Matrix.piAlgEquiv (β := M) (n := Fin (n i0)) F).symm (e1 (r ⊗ₜ[F] (1 : A))) := rfl
  rw [h3, AlgEquiv.apply_symm_apply]
  ext i : 1
  have h4 : e1 (r ⊗ₜ[F] (1 : A)) i = Matrix.reindexAlgEquiv F (M i) (finCongr (hall i))
      (hf i (r i ⊗ₜ[F] (1 : A))) := rfl
  rw [h4]
  have h5 : r i ⊗ₜ[F] (1 : A) = algebraMap (M i) (M i ⊗[F] A) (r i) := rfl
  rw [h5, AlgEquiv.commutes]
  ext a b
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
  split_ifs <;> rfl

/-- A central simple algebra is split by a finite product of fields exactly when it is split by every factor. -/
theorem splitsOverRing_pi_iff {ι : Type} [Fintype ι] [Nonempty ι] (M : ι → Type) [∀ i, Field (M i)]
    [∀ i, Algebra F (M i)] (A : CSA.{0, 0} F) :
    SplitsOverRing (∀ i, M i) A ↔ ∀ i, SplitsOverRing (M i) A :=
  ⟨fun h i ↦ h.of_algHom (Pi.evalAlgHom F M i), splitsOverRing_pi M A⟩

/-- The `n`-torsion of $\mathbb Q/\mathbb Z$ has `n` elements. -/
theorem natCard_torsion_QZ (n : ℕ) (hn : 0 < n) : Nat.card {q : QZ // n • q = 0} = n := by
  classical
  let g : ℕ → QZ := fun k => QuotientAddGroup.mk ((k : ℚ) / n)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgt : ∀ k, n • g k = 0 := by
    intro k
    show n • (QuotientAddGroup.mk ((k : ℚ) / n) : QZ) = 0
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    refine ⟨k, ?_⟩
    show ((k : ℤ) : ℚ) = n • ((k : ℚ) / n)
    rw [nsmul_eq_mul]; field_simp; simp
  have hinj : ∀ k l, k < n → l < n → g k = g l → k = l := by
    intro k l hk hl hkl
    have := QuotientAddGroup.eq.1 hkl
    obtain ⟨z, hz⟩ := this
    have hz' : (z : ℚ) = -((k : ℚ) / n) + (l : ℚ) / n := hz
    have h2 : (z : ℚ) * n = (l : ℚ) - k := by rw [hz']; field_simp; ring
    have h3 : z * (n : ℤ) = (l : ℤ) - k := by exact_mod_cast h2
    have hz0 : z = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · nlinarith
      · nlinarith
    subst hz0
    omega
  have hsurj : ∀ q : QZ, n • q = 0 → ∃ k, k < n ∧ g k = q := by
    intro q hq
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hq' : n • (QuotientAddGroup.mk r : QZ) = 0 := hq
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hq'
    obtain ⟨z, hz⟩ := hq'
    have hz' : (z : ℚ) = n * r := by
      have : (Int.castAddHom ℚ) z = n • r := hz
      simpa [nsmul_eq_mul] using this
    have hm0 : 0 ≤ z % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have hmn : z % (n : ℤ) < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    refine ⟨(z % (n : ℤ)).toNat, by omega, ?_⟩
    have hk : (((z % (n : ℤ)).toNat : ℕ) : ℚ) = ((z % (n : ℤ) : ℤ) : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hm0
    have hdiv : (z : ℚ) = n * ((z / (n : ℤ) : ℤ) : ℚ) + ((z % (n : ℤ) : ℤ) : ℚ) := by
      exact_mod_cast (Int.mul_ediv_add_emod z n).symm
    show QuotientAddGroup.mk (((z % (n : ℤ)).toNat : ℚ) / n) = QuotientAddGroup.mk r
    rw [QuotientAddGroup.eq]
    refine ⟨z / (n : ℤ), ?_⟩
    show (((z / (n : ℤ) : ℤ)) : ℚ) = -(((z % (n : ℤ)).toNat : ℚ) / n) + r
    rw [hk]
    field_simp
    linarith
  let F' : Fin n → {q : QZ // n • q = 0} := fun k => ⟨g k, hgt k⟩
  have hb : Function.Bijective F' := by
    constructor
    · intro k l hkl
      exact Fin.ext (hinj k l k.2 l.2 (congrArg Subtype.val hkl))
    · rintro ⟨q, hq⟩
      obtain ⟨k, hk, rfl⟩ := hsurj q hq
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective F' hb]
  simp

end NumberFieldKB.MilneCFT.Ch8
