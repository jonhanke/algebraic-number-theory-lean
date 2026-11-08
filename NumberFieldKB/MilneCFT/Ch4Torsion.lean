import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Lemma315
import NumberFieldKB.MilneCFT.Ch4Splitting

/-!
# Milne, Class Field Theory, Chapter IV, §3: Corollaries 3.16 and 3.17

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §3: compatibility of the isomorphisms $H^2(L/k) \cong \mathrm{Br}(L/k)$ with inflation
(Cor. 3.16) and torsion of the Brauer group (Cor. 3.17).

Cor. 3.16 (formalization at finite level).  Milne's $H^2(k^{\mathrm{al}}/k)$ is the direct limit of
the $H^2(L/k)$ along inflation, and his proof of the canonical isomorphism
$\mathrm{Br}(k) \cong H^2(k^{\mathrm{al}}/k)$ consists of (i) $\mathrm{Br}(k) = \bigcup \mathrm{Br}(L/k)$
(Cor. 3.10) and (ii) the commutativity of the inflation square (his footnote 5: "Should add a proof
that the diagram commutes").  We prove (ii) at the level of cocycles: the crossed product of the
inflation of $\varphi$ is similar to the crossed product of $\varphi$.

Cor. 3.17.  Milne's proof ("the same statements are true for the cohomology groups") covers
finite *Galois* extensions $L/k$, through Thm. 3.14 and the fact that $H^2(G, M)$ is killed by
$|G|$; the latter is proved here directly for normalized cocycles
($\varphi^{n} = \partial x$ with $x(\sigma) = \prod_\tau \varphi(\sigma, \tau)$).  For a finite extension
that is not Galois the statement needs that the exponent of a central simple algebra divides its
degree, which Milne does not prove; it is the named statement `ExponentDividesDegree`.

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u

section Generic

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

namespace NormalizedCocycle

/-- The trivial cocycle $\varphi = 1$. -/
def one : NormalizedCocycle K L :=
  ⟨fun _ => 1, by
    intro σ τ ρ
    simp, rfl⟩

/-- The $n$-th power of a normalized cocycle. -/
def npow (φ : NormalizedCocycle K L) : ℕ → NormalizedCocycle K L
  | 0 => one
  | n + 1 => mul (npow φ n) φ

theorem one_apply (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) : (one (K := K) (L := L)) p = 1 := rfl

theorem npow_apply (φ : NormalizedCocycle K L) (n : ℕ) (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) :
    (npow φ n) p = (φ p) ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    show (npow φ n) p * φ p = (φ p) ^ (n + 1)
    rw [ih, pow_succ]

theorem cohomologous_refl (φ : NormalizedCocycle K L) : Cohomologous φ φ :=
  ⟨fun _ => 1, fun g h => by simp⟩

/-- $H^2(G, L^\times)$ is killed by $|G|$, at the level of cocycles: $\varphi^{|G|}$ is cohomologous to
the trivial cocycle (with $x(\sigma) = \prod_\tau \varphi(\sigma, \tau)$). -/
theorem npow_card_cohomologous_one [FiniteDimensional K L] (φ : NormalizedCocycle K L) :
    Cohomologous (npow φ (Nat.card (L ≃ₐ[K] L))) one := by
  unfold Cohomologous
  refine ⟨fun σ => ∏ τ, φ (σ, τ), fun σ τ => ?_⟩
  have key : (∏ ρ, φ (σ * τ, ρ)) * (∏ _ρ : L ≃ₐ[K] L, φ (σ, τ)) =
      σ • (∏ ρ, φ (τ, ρ)) * ∏ ρ, φ (σ, τ * ρ) := by
    rw [← Finset.prod_mul_distrib, Finset.smul_prod', ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ρ _ => φ.cocycle σ τ ρ
  have h3 : ∏ ρ, φ (σ, τ * ρ) = ∏ ρ, φ (σ, ρ) :=
    Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
  rw [h3, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card] at key
  show σ • (∏ ρ, φ (τ, ρ)) / (∏ ρ, φ (σ * τ, ρ)) * ∏ ρ, φ (σ, ρ) =
    (npow φ (Nat.card (L ≃ₐ[K] L))) (σ, τ) / one (σ, τ)
  rw [npow_apply, one_apply, div_one, div_mul_eq_mul_div, div_eq_iff_eq_mul, mul_comm (σ • _), mul_comm _ (∏ ρ, φ (σ * τ, ρ))]
  exact (mul_comm _ _).trans key.symm

end NormalizedCocycle

variable [FiniteDimensional K L] [IsGalois K L]

namespace CrossedProduct

/-- The action of $A(1)$ on $L$: $a e_\sigma \mapsto (x \mapsto a\,\sigma(x))$. -/
noncomputable def evalOne (x : CrossedProduct (NormalizedCocycle.one (K := K) (L := L))) :
    Module.End K L :=
  ∑ σ : L ≃ₐ[K] L, x σ • (σ : L →ₐ[K] L).toLinearMap

theorem evalOne_apply (x : CrossedProduct (NormalizedCocycle.one (K := K) (L := L))) (y : L) :
    evalOne x y = ∑ σ : L ≃ₐ[K] L, x σ * σ y := by
  simp [evalOne]

theorem evalOne_mul (x y : CrossedProduct (NormalizedCocycle.one (K := K) (L := L))) :
    evalOne (x * y) = evalOne x * evalOne y := by
  ext z
  rw [Module.End.mul_apply, evalOne_apply, evalOne_apply]
  simp only [evalOne_apply, mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  refine (Equiv.sum_comp (Equiv.mulLeft σ) _).symm.trans (Finset.sum_congr rfl fun τ _ => ?_)
  simp [NormalizedCocycle.one_apply, mul_assoc]

/-- The map $A(1) \to \mathrm{End}_K(L)$ as a $K$-algebra homomorphism. -/
noncomputable def evalOneHom :
    CrossedProduct (NormalizedCocycle.one (K := K) (L := L)) →ₐ[K] Module.End K L :=
  AlgHom.ofLinearMap
    { toFun := evalOne
      map_add' := by
        intro x y
        ext z
        simp [evalOne_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        ext z
        have hs : ∀ σ, (r • x) σ = r • x σ := fun _ => rfl
        simp [evalOne_apply, hs, Finset.smul_sum, smul_mul_assoc] }
    (by
      ext z
      show evalOne (single _ 1 1) z = z
      rw [evalOne_apply]
      simp [single_apply]
      exact (Finset.sum_eq_single (1 : L ≃ₐ[K] L) (fun b _ hb => by simp [hb]) (by simp)).trans
        (by simp))
    evalOne_mul

theorem evalOneHom_bijective : Function.Bijective (evalOneHom (K := K) (L := L)) := by
  have hinj : Function.Injective (evalOneHom (K := K) (L := L)) :=
    (evalOneHom (K := K) (L := L)).toRingHom.injective
  refine ⟨hinj, ?_⟩
  have hfr : Module.finrank K (CrossedProduct (NormalizedCocycle.one (K := K) (L := L))) =
      Module.finrank K (Module.End K L) := by
    rw [finrank_eq]
    show _ = Module.finrank K (L →ₗ[K] L)
    rw [Module.finrank_linearMap, sq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
    (f := (evalOneHom (K := K) (L := L)).toLinearMap)).1 hinj

end CrossedProduct

/-- The crossed product of the trivial cocycle is split: $[A(1)] = 1$ (the map
$a e_\sigma \mapsto (x \mapsto a\,\sigma(x))$ is an isomorphism $A(1) \cong \mathrm{End}_K(L)$). -/
theorem mk_crossedProduct_one :
    BrauerGroup.mk (CrossedProduct.toCSA (NormalizedCocycle.one (K := K) (L := L))) = 1 := by
  rw [BrauerGroup.mk_eq_one_iff]
  refine ⟨Module.finrank K L, Module.finrank_pos.ne', ⟨?_⟩⟩
  exact (AlgEquiv.ofBijective _ CrossedProduct.evalOneHom_bijective).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K L))

/-- Every element of $\mathrm{Br}(L/K)$ is the class of a crossed product (Cor. 3.6 and
Thm. 3.11). -/
theorem exists_crossedProduct_of_mem_relBrauer (x : BrauerGroup.{u, u} K)
    (hx : x ∈ relBrauer K L) :
    ∃ φ : NormalizedCocycle K L, x = BrauerGroup.mk (CrossedProduct.toCSA φ) := by
  obtain ⟨A, rfl⟩ : ∃ A : CSA.{u, u} K, x = BrauerGroup.mk A := by
    induction x using Quotient.inductionOn with | _ A => exact ⟨A, rfl⟩
  obtain ⟨B, hAB, ⟨ι⟩, hdim⟩ := (cor_3_6 A L).1 ((mk_mem_relBrauer_iff L A).1 hx)
  have hB : IsInClassA (B : Type u) ι :=
    ⟨inferInstance, inferInstance, inferInstance, hdim⟩
  obtain ⟨φ, hφ⟩ := exists_isCocycleOf (B : Type u) ι hB
  obtain ⟨hA', hc'⟩ := thm_3_11_surj φ
  obtain ⟨e⟩ := (thm_3_11_fibres (B : Type u) (CrossedProduct φ) ι (CrossedProduct.incl φ) hB hA'
    φ φ hφ hc').2 (NormalizedCocycle.cohomologous_refl φ)
  refine ⟨φ, ?_⟩
  rw [BrauerGroup.mk_eq_mk_iff]
  exact (hAB.trans (isBrauerEquivalent_of_algEquiv (A := B) (B := CrossedProduct.toCSA φ) e))

/-- Classes of crossed products multiply like the cocycles (Lemma 3.15). -/
theorem mk_crossedProduct_npow (φ : NormalizedCocycle K L) (n : ℕ) :
    BrauerGroup.mk (CrossedProduct.toCSA (NormalizedCocycle.npow φ n)) =
      BrauerGroup.mk (CrossedProduct.toCSA φ) ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact mk_crossedProduct_one
  | succ n ih =>
    rw [pow_succ, ← ih, BrauerGroup.mk_mul_mk, BrauerGroup.mk_eq_mk_iff]
    exact lemma_3_15 _ _

/-- Cohomologous cocycles give isomorphic crossed products (Thm. 3.11). -/
theorem mk_crossedProduct_eq_of_cohomologous (φ φ' : NormalizedCocycle K L)
    (h : NormalizedCocycle.Cohomologous φ φ') :
    BrauerGroup.mk (CrossedProduct.toCSA φ) = BrauerGroup.mk (CrossedProduct.toCSA φ') := by
  obtain ⟨hA, hc⟩ := thm_3_11_surj φ
  obtain ⟨hA', hc'⟩ := thm_3_11_surj φ'
  obtain ⟨e⟩ := (thm_3_11_fibres _ _ _ _ hA hA' φ φ' hc hc').2 h
  rw [BrauerGroup.mk_eq_mk_iff]
  exact isBrauerEquivalent_of_algEquiv (A := CrossedProduct.toCSA φ) (B := CrossedProduct.toCSA φ') e

end Generic

/-! ### Corollary 3.16 -/

section Inflation

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] {E : Type u} [Field E]
  [Algebra K E] [Algebra L E] [IsScalarTower K L E] [FiniteDimensional K L] [FiniteDimensional K E]
  [IsGalois K L] [IsGalois K E]

/-- The inflation of a normalized cocycle of $\mathrm{Gal}(L/K)$ to $\mathrm{Gal}(E/K)$ for
$K \subseteq L \subseteq E$: $(\sigma, \tau) \mapsto \varphi(\sigma|_L, \tau|_L) \in L^\times \subseteq E^\times$. -/
noncomputable def NormalizedCocycle.inflate (φ : NormalizedCocycle K L) : NormalizedCocycle K E :=
  ⟨fun p => Units.map (algebraMap L E : L →* E) (φ (p.1.restrictNormal L, p.2.restrictNormal L)),
    by
    have hm : ∀ a b : E ≃ₐ[K] E, (a * b).restrictNormal L =
        a.restrictNormal L * b.restrictNormal L :=
      fun a b => map_mul (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L) a b
    intro σ τ ρ
    have h := congrArg Units.val
      (φ.cocycle (σ.restrictNormal L) (τ.restrictNormal L) (ρ.restrictNormal L))
    simp only [Units.val_mul, Units.smul_def] at h
    apply Units.ext
    simp only [Units.val_mul, Units.smul_def, Units.coe_map, MonoidHom.coe_coe, hm]
    have hs : ∀ u : Eˣ, ((σ • u : Eˣ) : E) = σ (u : E) := fun u => rfl
    rw [hs]
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [← AlgEquiv.restrictNormal_commutes, ← map_mul, ← map_mul]
    exact congrArg (algebraMap L E) h, by
    have h1 : (1 : E ≃ₐ[K] E).restrictNormal L = 1 :=
      map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L)
    show Units.map (algebraMap L E : L →* E) (φ ((1 : E ≃ₐ[K] E).restrictNormal L,
      (1 : E ≃ₐ[K] E).restrictNormal L)) = 1
    rw [h1, φ.map_one_one, map_one]⟩

namespace InflationAux

variable {κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ L E)

/-- The matrix of the (semilinear) automorphism $\sigma$ of $E$ in the $L$-basis $b$:
$\sigma(b_j) = \sum_i S_\sigma(i, j) b_i$. -/
noncomputable def Smat (σ : E ≃ₐ[K] E) : Matrix κ κ L := fun i j => b.repr (σ (b j)) i

theorem smul_apply' (σ : E ≃ₐ[K] E) (r : L) (x : E) :
    σ (r • x) = (σ.restrictNormal L r) • σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← AlgEquiv.restrictNormal_commutes]

theorem repr_apply (σ : E ≃ₐ[K] E) (y : E) (i : κ) :
    b.repr (σ y) i = ∑ j, σ.restrictNormal L (b.repr y j) * Smat b σ i j := by
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_apply', map_smul, Finsupp.smul_apply, smul_eq_mul]
  rfl

theorem mul_repr (z w : E) (i : κ) :
    b.repr (z * w) i = ∑ j, b.repr w j * b.repr (z * b j) i := by
  conv_lhs => rw [← b.sum_repr w]
  rw [Finset.mul_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem Smat_mul (σ τ : E ≃ₐ[K] E) (i k : κ) :
    Smat b (σ * τ) i k = ∑ j, σ.restrictNormal L (Smat b τ j k) * Smat b σ i j := by
  have := repr_apply b σ (τ (b k)) i
  exact this

theorem Smat_one (i j : κ) : Smat b (1 : E ≃ₐ[K] E) i j = if i = j then 1 else 0 := by
  simp [Smat, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

variable {A : Type u} [Ring A] [Algebra K A]

/-- The matrix $E_\sigma = (\iota(S_\sigma(i, j))) \cdot e_{\sigma|_L}$. -/
noncomputable def Emat (ι : L →ₐ[K] A) (e : (L ≃ₐ[K] L) → Aˣ) (σ : E ≃ₐ[K] E) : Matrix κ κ A :=
  fun i j => ι (Smat b σ i j) * (e (σ.restrictNormal L) : A)

/-- The embedding $E \to M_d(A)$ through the regular representation of $E$ over $L$. -/
noncomputable def jmap (ι : L →ₐ[K] A) : E →ₐ[K] Matrix κ κ A :=
  (AlgHom.mapMatrix ι).comp ((Algebra.leftMulMatrix b).restrictScalars K)

theorem jmap_apply (ι : L →ₐ[K] A) (x : E) (i j : κ) :
    jmap b ι x i j = ι (b.repr (x * b j) i) := by
  simp [jmap, Algebra.leftMulMatrix_eq_repr_mul]

theorem Emat_mul_jmap (ι : L →ₐ[K] A) (e : (L ≃ₐ[K] L) → Aˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ) (σ : E ≃ₐ[K] E) (x : E) :
    Emat b ι e σ * jmap b ι x = jmap b ι (σ x) * Emat b ι e σ := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Emat, jmap_apply]
  have h1 : ∀ j, ι (Smat b σ i j) * (e (σ.restrictNormal L) : A) *
      ι (b.repr (x * b k) j) =
      ι (b.repr (x * b k) j |> fun r => σ.restrictNormal L r * Smat b σ i j) *
        (e (σ.restrictNormal L) : A) := by
    intro j
    rw [mul_assoc, he, ← mul_assoc, ← map_mul, mul_comm]
  have h2 : ∀ j, ι (b.repr (σ x * b j) i) * (ι (Smat b σ j k) * (e (σ.restrictNormal L) : A)) =
      ι (Smat b σ j k * b.repr (σ x * b j) i) * (e (σ.restrictNormal L) : A) := by
    intro j
    rw [← mul_assoc, ← map_mul, mul_comm]
  simp only [h1, h2, ← Finset.sum_mul, ← map_sum]
  congr 2
  have := repr_apply b σ (x * b k) i
  rw [map_mul, mul_repr b (σ x) (σ (b k)) i] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

theorem restrictNormal_mul' (σ τ : E ≃ₐ[K] E) :
    (σ * τ).restrictNormal L = σ.restrictNormal L * τ.restrictNormal L :=
  map_mul (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L) σ τ

theorem jmap_algebraMap (ι : L →ₐ[K] A) (l : L) (i j : κ) :
    jmap b ι (algebraMap L E l) i j = if i = j then ι l else 0 := by
  rw [jmap_apply, ← Algebra.smul_def, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem Emat_mul_Emat (ι : L →ₐ[K] A) (e : (L ≃ₐ[K] L) → Aˣ) (φ' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ)
    (he2 : ∀ σ τ, (e σ : A) * e τ = ι (φ' (σ, τ)) * e (σ * τ)) (σ τ : E ≃ₐ[K] E) :
    Emat b ι e σ * Emat b ι e τ =
      jmap b ι (algebraMap L E (φ' (σ.restrictNormal L, τ.restrictNormal L))) *
        Emat b ι e (σ * τ) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Emat, jmap_algebraMap, ite_mul, zero_mul, restrictNormal_mul']
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  have h1 : ∀ j, ι (Smat b σ i j) * (e (σ.restrictNormal L) : A) *
      (ι (Smat b τ j k) * (e (τ.restrictNormal L) : A)) =
      ι (Smat b τ j k |> fun r => σ.restrictNormal L r * Smat b σ i j) *
        (ι (φ' (σ.restrictNormal L, τ.restrictNormal L)) *
          (e (σ.restrictNormal L * τ.restrictNormal L) : A)) := by
    intro j
    rw [← he2]
    calc ι (Smat b σ i j) * (e (σ.restrictNormal L) : A) *
          (ι (Smat b τ j k) * (e (τ.restrictNormal L) : A))
        = ι (Smat b σ i j) * ((e (σ.restrictNormal L) : A) * ι (Smat b τ j k)) *
            (e (τ.restrictNormal L) : A) := by simp only [mul_assoc]
      _ = _ := by
        rw [he, ← mul_assoc, ← map_mul, mul_comm (Smat b σ i j), mul_assoc]
  simp only [h1, ← Finset.sum_mul, ← map_sum]
  rw [← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, Smat_mul, mul_comm]

theorem Emat_one (ι : L →ₐ[K] A) (e : (L ≃ₐ[K] L) → Aˣ) (he1 : e 1 = 1) :
    Emat b ι e (1 : E ≃ₐ[K] E) = 1 := by
  ext i j
  have h1 : (1 : E ≃ₐ[K] E).restrictNormal L = 1 :=
    map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L)
  simp only [Emat, h1, he1, Smat_one]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

theorem isUnit_Emat (ι : L →ₐ[K] A) (e : (L ≃ₐ[K] L) → Aˣ)
    (φ' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ)
    (he2 : ∀ σ τ, (e σ : A) * e τ = ι (φ' (σ, τ)) * e (σ * τ)) (he1 : e 1 = 1)
    (σ : E ≃ₐ[K] E) : IsUnit (Emat b ι e σ) := by
  have hu : ∀ (α β : E ≃ₐ[K] E), α * β = 1 → IsUnit (Emat b ι e α * Emat b ι e β) := by
    intro α β h
    rw [Emat_mul_Emat b ι e φ' he he2, h, Emat_one b ι e he1, mul_one]
    exact ((Units.map (algebraMap L E : L →* E) (φ' (α.restrictNormal L, β.restrictNormal L))).isUnit.map
      (jmap b ι : E →* Matrix κ κ A))
  obtain ⟨u, hu1⟩ := hu σ σ⁻¹ (mul_inv_cancel σ)
  obtain ⟨v, hv1⟩ := hu σ⁻¹ σ (inv_mul_cancel σ)
  rw [isUnit_iff_exists]
  have h1 : ((v⁻¹ : (Matrix κ κ A)ˣ) : Matrix κ κ A) * Emat b ι e σ⁻¹ * Emat b ι e σ = 1 := by
    rw [mul_assoc, ← hv1]; simp
  have h2 : Emat b ι e σ * (Emat b ι e σ⁻¹ * ((u⁻¹ : (Matrix κ κ A)ˣ) : Matrix κ κ A)) = 1 := by
    rw [← mul_assoc, ← hu1]; simp
  refine ⟨Emat b ι e σ⁻¹ * ((u⁻¹ : (Matrix κ κ A)ˣ) : Matrix κ κ A), h2, ?_⟩
  have : (((v⁻¹ : (Matrix κ κ A)ˣ) : Matrix κ κ A) * Emat b ι e σ⁻¹) =
      Emat b ι e σ⁻¹ * ((u⁻¹ : (Matrix κ κ A)ˣ) : Matrix κ κ A) :=
    left_inv_eq_right_inv h1 h2
  rw [← this]; exact h1

theorem isCocycleOf_matrix (ι : L →ₐ[K] A) (e : (L ≃ₐ[K] L) → Aˣ)
    (φ' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ)
    (he2 : ∀ σ τ, (e σ : A) * e τ = ι (φ' (σ, τ)) * e (σ * τ)) (he1 : e 1 = 1) :
    IsCocycleOf (Matrix κ κ A) (jmap b ι)
      (fun p : (E ≃ₐ[K] E) × (E ≃ₐ[K] E) =>
        Units.map (algebraMap L E : L →* E) (φ' (p.1.restrictNormal L, p.2.restrictNormal L))) := by
  refine ⟨fun σ => (isUnit_Emat b ι e φ' he he2 he1 σ).unit, fun σ a => ?_, fun σ τ => ?_⟩
  · simp only [IsUnit.unit_spec]
    exact Emat_mul_jmap b ι e he σ a
  · simp only [IsUnit.unit_spec]
    exact Emat_mul_Emat b ι e φ' he he2 σ τ

end InflationAux

/-- Corollary 3.16 of Milne, at finite level: for a tower $K \subseteq L \subseteq E$ of finite Galois
extensions, the square formed by inflation $H^2(L/K) \to H^2(E/K)$ and the maps
$\varphi \mapsto [A(\varphi)]$ commutes: $[A(\mathrm{Inf}\,\varphi)] = [A(\varphi)]$ in $\mathrm{Br}(K)$.  With
Cor. 3.10 this gives the canonical isomorphism $\mathrm{Br}(k) \cong H^2(k^{\mathrm{al}}/k)$ of direct
limits. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.16, p. 138"]
theorem cor_3_16 (φ : NormalizedCocycle K L) :
    BrauerGroup.mk (CrossedProduct.toCSA (NormalizedCocycle.inflate (E := E) φ)) =
      BrauerGroup.mk (CrossedProduct.toCSA φ) := by
  haveI : Module.Finite L E := Module.Finite.of_restrictScalars_finite K L E
  let b := Module.finBasis L E
  haveI : Nonempty (Fin (Module.finrank L E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  obtain ⟨hA, e, he, he2⟩ := thm_3_11_surj φ
  have he1 : e 1 = 1 := by
    have h := he2 1 1
    rw [mul_one, φ.map_one_one] at h
    have h' : (e 1 : CrossedProduct φ) * e 1 = 1 * e 1 := by
      rw [h]; simp
    have h'' : e 1 * e 1 = e 1 := Units.ext (by simpa using h')
    exact mul_left_cancel (a := e 1) (by rw [mul_one]; exact h'')
  have hM := InflationAux.isCocycleOf_matrix (E := E) b (CrossedProduct.incl φ) e φ.toFun he he2
    he1
  have hMclass : IsInClassA (Matrix (Fin (Module.finrank L E)) (Fin (Module.finrank L E))
      (CrossedProduct φ)) (InflationAux.jmap b (CrossedProduct.incl φ)) := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    have h1 : Module.finrank K (Matrix (Fin (Module.finrank L E)) (Fin (Module.finrank L E))
        (CrossedProduct φ)) = Module.finrank L E * (Module.finrank L E *
          Module.finrank K (CrossedProduct φ)) := by
      show Module.finrank K (Fin (Module.finrank L E) → Fin (Module.finrank L E) →
        CrossedProduct φ) = _
      simp [Module.finrank_pi_fintype]
    rw [h1, hA.finrank_eq, ← Module.finrank_mul_finrank K L E]
    ring
  obtain ⟨hC, hCc⟩ := thm_3_11_surj (NormalizedCocycle.inflate (E := E) φ)
  obtain ⟨eMC⟩ := (thm_3_11_fibres _ _ (InflationAux.jmap b (CrossedProduct.incl φ))
    (CrossedProduct.incl (NormalizedCocycle.inflate (E := E) φ)) hMclass hC
    (NormalizedCocycle.inflate (E := E) φ) (NormalizedCocycle.inflate (E := E) φ) hM hCc).2
    (NormalizedCocycle.cohomologous_refl _)
  rw [BrauerGroup.mk_eq_mk_iff]
  refine ⟨1, Module.finrank L E, one_ne_zero, Module.finrank_pos.ne', ⟨?_⟩⟩
  exact (BrauerGroup.matOne (CrossedProduct (NormalizedCocycle.inflate (E := E) φ))).trans
    eMC.symm

end Inflation

/-! ### Corollary 3.17 -/

section Torsion

variable {K : Type u} [Field K]

/-- Corollary 3.17 of Milne for a finite Galois extension $L/K$: $\mathrm{Br}(L/K)$ is killed by
$[L : K]$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.17 (Galois case), p. 138"]
theorem cor_3_17_galois (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (x : BrauerGroup.{u, u} K) (hx : x ∈ relBrauer K L) :
    x ^ Module.finrank K L = 1 := by
  obtain ⟨φ, rfl⟩ := exists_crossedProduct_of_mem_relBrauer x hx
  rw [← IsGalois.card_aut_eq_finrank K L, ← mk_crossedProduct_npow,
    mk_crossedProduct_eq_of_cohomologous _ _ (NormalizedCocycle.npow_card_cohomologous_one φ)]
  exact mk_crossedProduct_one

/-- Corollary 3.17 of Milne, first assertion: $\mathrm{Br}(K)$ is a torsion group. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.17 (Br(k) torsion), p. 138"]
theorem cor_3_17_torsion (x : BrauerGroup.{u, u} K) : IsOfFinOrder x := by
  obtain ⟨L, hfd, hG, hx⟩ := cor_3_10 x
  have h := cor_3_17_galois (K := K) (↥L) x hx
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, Module.finrank_pos, h⟩

/-- The exponent of a central simple algebra divides its degree (named statement): if
$[A : K] = n^2$ then $[A]^n = 1$ in $\mathrm{Br}(K)$.  Needed for Cor. 3.17 over a finite extension
that is not Galois; Milne's proof does not cover that case (see the module docstring). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.17 (non-Galois case; exponent divides degree), p. 138"]
structure ExponentDividesDegree (K : Type u) [Field K] : Prop where
  pow_deg_eq_one : ∀ (A : CSA.{u, u} K) (n : ℕ), Module.finrank K A = n ^ 2 →
    BrauerGroup.mk A ^ n = 1

/-- Corollary 3.17 of Milne, second assertion, for every finite extension $L/K$: $\mathrm{Br}(L/K)$ is
killed by $[L : K]$ (from Cor. 3.6 and the named statement `ExponentDividesDegree`). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Cor. 3.17, p. 138"]
theorem cor_3_17 (h : ExponentDividesDegree K) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : BrauerGroup.{u, u} K) (hx : x ∈ relBrauer K L) :
    x ^ Module.finrank K L = 1 := by
  obtain ⟨A, rfl⟩ : ∃ A : CSA.{u, u} K, x = BrauerGroup.mk A := by
    induction x using Quotient.inductionOn with | _ A => exact ⟨A, rfl⟩
  obtain ⟨B, hAB, -, hdim⟩ := (cor_3_6 A L).1 ((mk_mem_relBrauer_iff L A).1 hx)
  rw [(BrauerGroup.mk_eq_mk_iff A B).2 hAB]
  exact h.pow_deg_eq_one B _ hdim

end Torsion

end NumberFieldKB.MilneCFT.Ch4
