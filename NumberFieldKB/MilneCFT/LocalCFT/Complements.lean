import NumberFieldKB.MilneCFT.LocalCFT.Consequences
import NumberFieldKB.MilneCFT.LubinTate.Extension
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Normal.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.PowerSubgroup.Open

/-!
# Complements to local class field theory (Milne, *Class Field Theory*, Introduction and Chapter I, §1)

* **Theorem 0.9 (Hasse)** (`hasse_theorem`): for $K$ of characteristic zero, $L \mapsto \mathrm{Nm}(L^\times)$ is an
  order-reversing bijection from the finite abelian extensions onto the subgroups of finite index — from Theorem 1.1,
  Theorem 1.4 and the named statement `FiniteIndexOpenInput` (Milne, I, 1.7: in characteristic zero every subgroup of
  finite index is open).
* **The local Artin map for $\mathbb R$** (Milne, I, 1.6): `realArtin`, the isomorphism
  $\mathbb R^\times/\mathbb R_{>0} \to \mathrm{Gal}(\mathbb C/\mathbb R)$ (unique: `realArtin_unique`).
* **Exercise 1.16** (named statement `TotallyRamifiedNormInput`): $L/K$ is totally ramified iff
  $\mathrm{Nm}(L^\times)$ contains a prime element.
* **The Weil group** (Introduction, p. 15): `weilGroup`.

**Appendix A of Chapter I (definitions in prose; all in Mathlib).** Galois extension: `IsGalois`; Krull topology:
`krullTopology` (compact, Hausdorff: `InfiniteGalois` instances in `Mathlib/FieldTheory/Galois/Profinite.lean`);
the infinite Galois correspondence: `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`; directed sets:
`IsDirected`; inverse limits: `CategoryTheory.Limits.limit`, `ProfiniteGrp.limit`; profinite completion:
`ProfiniteGrp.ProfiniteCompletion.completion`; profinite groups: `ProfiniteGrp`.

**Chapter I, prose definitions in Mathlib.** Prime element of a local field: `Irreducible` in `𝒪[K]`
(`Valuation.IsUniformizer`); the local field structure: `IsNonarchimedeanLocalField`.
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-! ## Theorem 0.9 -/

variable (K) in
/-- **Every subgroup of finite index is open in characteristic zero** (named statement; Milne, *CFT*, I, 1.7: a
subgroup $H$ of finite index contains $K^{\times m}$ for some $m$, and Newton's lemma applied to $X^m - a$ shows that
$K^{\times m}$ contains a neighbourhood of $1$).

**Proved here** as `finiteIndexOpenInput`, from the ported copy under `NumberFieldKB/TauCetiPort/` of Tau Ceti
`TauCeti.isOpen_of_natCast_index_ne_zero` (`TauCeti/NumberTheory/LocalField/PowerSubgroup/Open.lean:79`) (read at Tau Ceti `7ed979dc`, ported from `67aa1716`). Needed to apply it here: Tau Ceti assumes that the index, viewed in the field, is nonzero; in
characteristic zero this is automatic for a subgroup of finite index. -/
@[kb "milne2020cft" "Ch. I, 1.7 (finite index subgroups are open in characteristic zero; input)"]
structure FiniteIndexOpenInput : Prop where
  isOpen : CharZero K → ∀ H : Subgroup Kˣ, H.FiniteIndex → IsOpen (H : Set Kˣ)

variable (K) in
/-- **Milne, I, 1.7, proved**: the named statement `FiniteIndexOpenInput` holds, from Tau Ceti's
`TauCeti.isOpen_of_natCast_index_ne_zero` (ported, `NumberFieldKB/TauCetiPort/NumberTheory/LocalField/PowerSubgroup/Open.lean`):
a subgroup whose index is nonzero in $K$ is open, and in characteristic zero a finite index is nonzero in $K$. -/
@[kb "milne2020cft" "Ch. I, 1.7 (finite index subgroups are open in characteristic zero)"]
theorem finiteIndexOpenInput : FiniteIndexOpenInput K :=
  ⟨fun _ H hH => TauCeti.isOpen_of_natCast_index_ne_zero (Nat.cast_ne_zero.2 hH.index_ne_zero)⟩

/-- **Theorem 0.9 (Hasse 1930)** (Milne, *CFT*, Introduction): let $K$ be a local field of characteristic zero (a
finite extension of $\mathbb Q_p$). For every finite abelian extension $L$ of $K$, $\mathrm{Nm}(L^\times)$ has finite
index in $K^\times$, and $L \mapsto \mathrm{Nm}(L^\times)$ is an order-reversing bijection from the finite abelian
extensions of $K$ onto the subgroups of $K^\times$ of finite index. Conditional on Theorem 1.1 (existence) and the
hard half of Theorem 1.4; 1.7 is proved (`finiteIndexOpenInput`). -/
@[kb "milne2020cft" "Introduction, Theorem 0.9"]
theorem hasse_theorem [CharZero K] (h1 : LocalReciprocityExistence K Ω) (h4 : LocalExistenceInput K Ω) :
    (∀ L : FiniteAbelianExt K Ω, (normGroup L.toField).FiniteIndex) ∧
    (∀ L L' : FiniteAbelianExt K Ω, L.toField ≤ L'.toField ↔ normGroup L'.toField ≤ normGroup L.toField) ∧
    (∀ H : Subgroup Kˣ, H.FiniteIndex → ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = H ∧
      ∀ L' : FiniteAbelianExt K Ω, normGroup L'.toField = H → L'.toField = L.toField) := by
  obtain ⟨φ, hφ⟩ := h1.exists_artin
  refine ⟨fun L => ⟨by rw [index_normGroup hφ L]; exact Module.finrank_pos.ne'⟩,
    le_iff_normGroup_le hφ, fun H hH => ?_⟩
  exact existsUnique_normGroup_eq h1 h4 H ((finiteIndexOpenInput K).isOpen inferInstance H hH) hH

/-! ## The local Artin map for $\mathbb R$ -/

/-- **The local Artin map for $\mathbb R$** (Milne, *CFT*, I, 1.6): $\mathbb R^\times \to \mathrm{Gal}(\mathbb C/\mathbb R)$,
$a \mapsto 1$ for $a > 0$ and complex conjugation for $a < 0$; it induces the isomorphism
$\mathbb R^\times/\mathbb R_{>0} \cong \mathrm{Gal}(\mathbb C/\mathbb R)$ (`realArtin_ker`, `realArtin_surjective`). -/
@[kb "milne2020cft" "Ch. I, 1.6 (the local Artin map for R)"]
def realArtin : ℝˣ →* (ℂ ≃ₐ[ℝ] ℂ) where
  toFun a := if 0 < (a : ℝ) then 1 else Complex.conjAe
  map_one' := by simp
  map_mul' a b := by
    have hneg : ∀ c : ℝˣ, ¬ 0 < (c : ℝ) → (c : ℝ) < 0 := fun c h =>
      lt_of_le_of_ne (not_lt.1 h) c.ne_zero
    have hmul : ((a * b : ℝˣ) : ℝ) = (a : ℝ) * b := Units.val_mul a b
    have hc : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) * Complex.conjAe = 1 := by
      ext z; simp
    by_cases ha : 0 < (a : ℝ) <;> by_cases hb : 0 < (b : ℝ)
    · simp [ha, hb, hmul, mul_pos ha hb]
    · have := hneg b hb
      have : ¬ 0 < (a : ℝ) * b := not_lt.2 (mul_neg_of_pos_of_neg ha this).le
      simp [ha, hb, hmul, this]
    · have := hneg a ha
      have : ¬ 0 < (a : ℝ) * b := not_lt.2 (mul_neg_of_neg_of_pos this hb).le
      simp [ha, hb, hmul, this]
    · have h1 := hneg a ha
      have h2 := hneg b hb
      have : 0 < (a : ℝ) * b := mul_pos_of_neg_of_neg h1 h2
      simp [ha, hb, hmul, this, hc]

theorem realArtin_conj_ne_one : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) ≠ 1 := by
  intro h
  have := congrArg (fun f : ℂ ≃ₐ[ℝ] ℂ => f Complex.I) h
  simp only [Complex.conjAe_coe, AlgEquiv.one_apply, Complex.conj_I] at this
  have h2 := congrArg Complex.im this
  norm_num at h2

theorem realArtin_ker : realArtin.ker = {a : ℝˣ | 0 < (a : ℝ)} := by
  ext a
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  show realArtin a = 1 ↔ 0 < (a : ℝ)
  by_cases ha : 0 < (a : ℝ)
  · simp [realArtin, ha]
  · simp only [realArtin, MonoidHom.coe_mk, OneHom.coe_mk, ha, ite_false, iff_false]
    exact realArtin_conj_ne_one

theorem realArtin_alg_cases (g : ℂ ≃ₐ[ℝ] ℂ) : g = 1 ∨ g = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj (g : ℂ →ₐ[ℝ] ℂ) with h | h
  · left; ext z; exact DFunLike.congr_fun h z
  · right; ext z; exact DFunLike.congr_fun h z

theorem realArtin_surjective : Function.Surjective realArtin := by
  intro f
  rcases realArtin_alg_cases f with h | h
  · exact ⟨1, by simp [h]⟩
  · refine ⟨-1, ?_⟩
    simp [realArtin, h]

/-- **Uniqueness of the local Artin map for $\mathbb R$** (Milne, *CFT*, I, 1.6: "the unique isomorphism"): a
surjective homomorphism $\mathbb R^\times \to \mathrm{Gal}(\mathbb C/\mathbb R)$ with kernel $\mathbb R_{>0}$ is
`realArtin`. -/
@[kb "milne2020cft" "Ch. I, 1.6 (uniqueness of the local Artin map for R)"]
theorem realArtin_unique (ψ : ℝˣ →* (ℂ ≃ₐ[ℝ] ℂ)) (hker : ψ.ker = {a : ℝˣ | 0 < (a : ℝ)})
    (hψ : Function.Surjective ψ) : ψ = realArtin := by
  ext a : 1
  by_cases ha : 0 < (a : ℝ)
  · have h1 : ψ a = 1 := by
      have : a ∈ ψ.ker := by rw [← SetLike.mem_coe, hker]; exact ha
      exact this
    simp [realArtin, ha, h1]
  · have h1 : ψ a ≠ 1 := by
      intro h
      have : a ∈ ψ.ker := h
      rw [← SetLike.mem_coe, hker] at this
      exact ha this
    rcases realArtin_alg_cases (ψ a) with h | h
    · exact absurd h h1
    · simp [realArtin, ha, h]

/-- **The norm groups of $\mathbb R$** (Milne, *CFT*, I, 1.6): the only subgroups of finite index of $\mathbb R^\times$
are $\mathbb R^\times$ and $\mathbb R_{>0}$. -/
@[kb "milne2020cft" "Ch. I, 1.6 (subgroups of finite index of R^×)"]
theorem real_finiteIndex (H : Subgroup ℝˣ) (hH : H.FiniteIndex) :
    H = ⊤ ∨ (H : Set ℝˣ) = {a : ℝˣ | 0 < (a : ℝ)} := by
  haveI : H.Normal := Subgroup.normal_of_comm H
  have hm : H.index ≠ 0 := hH.index_ne_zero
  have hpos : ∀ a : ℝˣ, 0 < (a : ℝ) → a ∈ H := by
    intro a ha
    set m := H.index
    have hx : 0 < (a : ℝ) ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos ha _
    let b : ℝˣ := Units.mk0 _ hx.ne'
    have hb : b ^ m = a := by
      ext
      simp only [Units.val_pow_eq_pow_val, b, Units.val_mk0]
      exact Real.rpow_inv_natCast_pow ha.le hm
    rw [← hb]
    exact Subgroup.pow_index_mem H b
  by_cases hex : ∃ c : ℝˣ, ¬ 0 < (c : ℝ) ∧ c ∈ H
  · left
    obtain ⟨c, hc, hcH⟩ := hex
    have hcn : (c : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 hc) c.ne_zero
    rw [eq_top_iff]
    intro x _
    by_cases hx : 0 < (x : ℝ)
    · exact hpos x hx
    · have hxn : (x : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 hx) x.ne_zero
      have : x = c * (c⁻¹ * x) := by group
      rw [this]
      refine H.mul_mem hcH (hpos _ ?_)
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos_of_neg_of_neg (inv_lt_zero.2 hcn) hxn
  · right
    push_neg at hex
    ext a
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hn
      exact absurd h (hex a (not_lt.1 hn) |> fun h2 => by simpa using h2)
    · exact hpos a

/-! ## Exercise 1.16 -/

variable (K Ω) in
/-- **Exercise 1.16** (named statement; Milne, *CFT*, I, Exercise 1.16): a finite extension $L/K$ of local fields is
totally ramified if and only if $\mathrm{Nm}(L^\times)$ contains a prime element of $K$. -/
@[kb "milne2020cft" "Ch. I, Exercise 1.16 (input)"]
structure TotallyRamifiedNormInput : Prop where
  iff : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L],
    IsTotallyRamifiedExt L ↔ ∃ (π : 𝒪[K]) (hπ : Irreducible π), primeUnit hπ ∈ normGroup L

/-! ## The Weil group -/

variable (K Ω) in
/-- **The Weil group** $W_K$ (Milne, *CFT*, Introduction, p. 15): the elements of $\mathrm{Gal}(K^{\mathrm{al}}/K)$
acting on the residue field as an integer power of the Frobenius element; i.e. there is $n \in \mathbb Z$ such that
on every finite unramified (normal) extension $L$, $\sigma|_L = \mathrm{Frob}_{L/K}^n$. -/
@[kb "milne2020cft" "Introduction, p. 15 (the Weil group W_K)"]
def weilGroup : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∃ n : ℤ, ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L],
    IsUnramifiedExt L → ∀ τ : Gal(L/K), IsFrobenius L τ → AlgEquiv.restrictNormal σ L = τ ^ n}
  mul_mem' := by
    rintro σ σ' ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, fun L _ _ hL τ hτ => ?_⟩
    have h1 : AlgEquiv.restrictNormal (σ * σ') L =
        AlgEquiv.restrictNormal σ L * AlgEquiv.restrictNormal σ' L :=
      map_mul (AlgEquiv.restrictNormalHom L) σ σ'
    rw [h1, hn L hL τ hτ, hm L hL τ hτ, zpow_add]
  one_mem' := ⟨0, fun L _ _ _ τ _ => by
    have h1 : AlgEquiv.restrictNormal (1 : Ω ≃ₐ[K] Ω) L = 1 :=
      map_one (AlgEquiv.restrictNormalHom L)
    rw [h1, zpow_zero]⟩
  inv_mem' := by
    rintro σ ⟨n, hn⟩
    refine ⟨-n, fun L _ _ hL τ hτ => ?_⟩
    have h1 : AlgEquiv.restrictNormal σ⁻¹ L = (AlgEquiv.restrictNormal σ L)⁻¹ :=
      map_inv (AlgEquiv.restrictNormalHom L) σ
    rw [h1, hn L hL τ hτ, zpow_neg]

end NumberFieldKB.MilneCFT.LocalCFT
