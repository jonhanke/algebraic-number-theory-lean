import NumberFieldKB.MilneCFT.Ch8.LSeries

/-!
# Artin's induction theorem, unconditionally (Milne, *CFT*, VIII, §10, p. 262)

Proves `ArtinInduction` (class-function form): for a finite group `G` and `ρ : G →* GL_n(ℂ)`, the character
`χ(g) = tr ρ(g)` is in the `ℚ`-span of the functions `Ind_C ψ`, `C ≤ G` cyclic, `ψ : C →* ℂˣ`.

## Proof

Write `Ind_C f (g) = |C|⁻¹ ∑_{x ∈ G, x g x⁻¹ ∈ C} f(x g x⁻¹)` (`indFun`), linear in `f`, and
`θ_C(c) = |C|` if `c` generates `C`, `0` otherwise (`theta`).

1. (`sum_indFun_theta`) For a class function `χ`, `∑_{C cyclic} Ind_C(θ_C · χ|_C) = |G| χ`: for each `x`,
   `x g x⁻¹` generates exactly one cyclic subgroup, `zpowers (x g x⁻¹)` (`gen_iff`).
2. (`theta_mul_trace_mem`) For a cyclic group `C` and `A : C →* GL_n(ℂ)`, `θ_C · tr A` is a `ℚ`-combination of
   characters `C →* ℂˣ` (`charSpan`):
   * `tr A(g^k) = ∑_λ d_λ λ^k` with `d_λ ∈ ℕ`, `λ^|C| = 1` (`trace_matrix_pow_eq_sum`: `A(g)` is semisimple
     since `X^m - 1` is separable; trace is the sum of traces on the eigenspaces), and each `λ` is a power of a
     faithful character, so `tr A` is an `ℕ`-combination of characters;
   * `θ_C` is a `ℚ`-combination of characters (`theta_mem_charSpan`): Möbius inversion
     `θ_C = |C| ∑_{d ∣ m} μ(d) 1_{c^{m/d} = 1}` (`sum_moebius_divisors`) and `1_{c^e = 1}` is
     `d⁻¹ ∑_{l<d} ψ₁^{e l}` for a faithful character `ψ₁` (`indicator_mem_charSpan`, geometric sum);
   * a product of characters is a character (`mul_char_mem_charSpan`).
3. (`indFun_mem_inducedSpan`, `artinInduction`) `Ind_C` maps `charSpan C` into the target span, and
   `χ = |G|⁻¹ ∑_C Ind_C(θ_C χ|_C)`.
-/

open Polynomial
open scoped Classical
noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

lemma trace_pow_eq_sum_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {m : ℕ} (hm : 0 < m) (hf : f ^ m = 1) :
    ∃ (s : Finset ℂ) (d : ℂ → ℕ), (∀ l ∈ s, l ^ m = 1) ∧
      ∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = ∑ l ∈ s, (d l : ℂ) * l ^ k := by
  classical
  have hsq : Squarefree (X ^ m - 1 : ℂ[X]) := by
    have h : (X ^ m - C 1 : ℂ[X]).Separable :=
      Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero
    simpa using h.squarefree
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hf])
  have hsup := hss.iSup_eigenspace_eq_top
  have hind := f.eigenspaces_iSupIndep
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  have hfin : {μ | f.eigenspace μ ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hpow : ∀ (k : ℕ) (μ : ℂ) (x : V), x ∈ f.eigenspace μ → (f ^ k) x = μ ^ k • x := by
    intro k μ x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hx, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hmaps : ∀ (k : ℕ) (μ : ℂ), Set.MapsTo (f ^ k) (f.eigenspace μ) (f.eigenspace μ) := by
    intro k μ x hx
    rw [SetLike.mem_coe] at hx ⊢
    rw [hpow k μ x hx]
    exact Submodule.smul_mem _ _ hx
  refine ⟨hfin.toFinset, fun μ => Module.finrank ℂ (f.eigenspace μ), ?_, ?_⟩
  · intro μ hμ
    have hne : f.eigenspace μ ≠ ⊥ := by simpa using hμ
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    have h1 : (f ^ m) v = μ ^ m • v := hpow m μ v hv
    rw [hf] at h1
    have : (μ ^ m - 1) • v = 0 := by rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  · intro k
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (hmaps k)]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have : (f ^ k).restrict (hmaps k μ) = (μ ^ k) • LinearMap.id := by
      ext x
      exact hpow k μ x x.2
    rw [this, map_smul, LinearMap.trace_id]
    simp [mul_comm]

lemma trace_matrix_pow_eq_sum {n m : ℕ} (hm : 0 < m) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M ^ m = 1) :
    ∃ (s : Finset ℂ) (d : ℂ → ℕ), (∀ l ∈ s, l ^ m = 1) ∧
      ∀ k : ℕ, Matrix.trace (M ^ k) = ∑ l ∈ s, (d l : ℂ) * l ^ k := by
  have hpow : ∀ k : ℕ, (Matrix.toLin' M) ^ k = Matrix.toLin' (M ^ k) := by
    intro k
    exact (map_pow (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ))
      M k).symm
  obtain ⟨s, d, hs, h⟩ := trace_pow_eq_sum_eigen (Matrix.toLin' M) hm (by rw [hpow, hM, Matrix.toLin'_one]; rfl)
  refine ⟨s, d, hs, fun k => ?_⟩
  rw [← h k, hpow, Matrix.trace_toLin'_eq]

section Cyclic

/-- The functions `C → ℂ` which are characters. -/
def charSet (C : Type) [Group C] : Set (C → ℂ) :=
  {f | ∃ ψ : C →* ℂˣ, f = fun c => (ψ c : ℂ)}

/-- The `ℚ`-span of the characters of `C`. -/
def charSpan (C : Type) [Group C] : Submodule ℚ (C → ℂ) := Submodule.span ℚ (charSet C)

lemma exists_faithful_char (C : Type) [Group C] [Fintype C] [IsCyclic C] :
    ∃ ψ : C →* ℂˣ, Function.Injective ψ := by
  haveI : NeZero (Nat.card C) := ⟨Nat.card_pos.ne'⟩
  let e := zmodCyclicMulEquiv (inferInstance : IsCyclic C)
  let φ : Multiplicative (ZMod (Nat.card C)) →* ℂ := AddChar.toMonoidHom ZMod.stdAddChar
  have hφ : Function.Injective φ.toHomUnits := by
    intro x y hxy
    have : φ x = φ y := by simpa using congrArg Units.val hxy
    exact ZMod.injective_stdAddChar this
  exact ⟨φ.toHomUnits.comp e.symm.toMonoidHom, hφ.comp e.symm.injective⟩

lemma indicator_mem_charSpan {C : Type} [Group C] [Fintype C] (ψ₁ : C →* ℂˣ)
    (hinj : Function.Injective ψ₁) {e : ℕ} (he : e ∣ Fintype.card C) :
    (fun c : C => if c ^ e = 1 then (1 : ℂ) else 0) ∈ charSpan C := by
  classical
  obtain ⟨d, hd⟩ := he
  have hm : 0 < Fintype.card C := Fintype.card_pos
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h] at hd
    · exact h
  have key : (fun c : C => if c ^ e = 1 then (1 : ℂ) else 0) =
      ((d : ℚ)⁻¹) • ∑ l ∈ Finset.range d, (fun c : C => (((ψ₁ ^ (e * l)) c : ℂˣ) : ℂ)) := by
    funext c
    simp only [Pi.smul_apply, Finset.sum_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
      pow_mul]
    have hx : ((ψ₁ c : ℂ) ^ e) ^ d = 1 := by
      rw [← pow_mul, ← hd, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one]
      simp
    have hiff : (ψ₁ c : ℂ) ^ e = 1 ↔ c ^ e = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, Units.val_eq_one]
      constructor
      · intro h1; exact (injective_iff_map_eq_one ψ₁).mp hinj _ h1
      · intro h1; rw [h1]; simp
    by_cases hc : c ^ e = 1
    · have h1 : (ψ₁ c : ℂ) ^ e = 1 := hiff.mpr hc
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
      simp [hc, h1, Rat.smul_def, hd0]
    · have h1 : (ψ₁ c : ℂ) ^ e ≠ 1 := fun h => hc (hiff.mp h)
      simp only [hc, if_false]
      rw [geom_sum_eq h1, hx]
      simp
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l _ => ?_)
  exact Submodule.subset_span ⟨ψ₁ ^ (e * l), rfl⟩

lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    (ArithmeticFunction.moebius_mul_coe_zeta)
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- The function `θ_C`: `|C|` on generators, `0` elsewhere. -/
def theta (C : Type) [Group C] [Fintype C] : C → ℂ :=
  fun c => if orderOf c = Fintype.card C then (Fintype.card C : ℂ) else 0

lemma theta_mem_charSpan {C : Type} [Group C] [Fintype C] (ψ₁ : C →* ℂˣ)
    (hinj : Function.Injective ψ₁) : theta C ∈ charSpan C := by
  set m := Fintype.card C with hmdef
  have hm : 0 < m := Fintype.card_pos
  have key : theta C = ∑ d ∈ m.divisors, (((m : ℤ) * ArithmeticFunction.moebius d : ℤ) : ℚ) •
      (fun c : C => if c ^ (m / d) = 1 then (1 : ℂ) else 0) := by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def]
    set o := orderOf c with ho
    have hom : o ∣ m := orderOf_dvd_card
    have hopos : 0 < o := orderOf_pos c
    have hiff : ∀ d ∈ m.divisors, (c ^ (m / d) = 1 ↔ d ∣ m / o) := by
      intro d hd
      have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
      rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_div_iff_mul_dvd hdm, Nat.dvd_div_iff_mul_dvd hom,
        mul_comm]
    have hfilt : m.divisors.filter (fun d => d ∣ m / o) = (m / o).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      have hq : m / o ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm hom) hopos).ne'
      constructor
      · rintro ⟨⟨_, _⟩, h⟩; exact ⟨h, hq⟩
      · rintro ⟨h, _⟩; exact ⟨⟨h.trans (Nat.div_dvd_of_dvd hom), hm.ne'⟩, h⟩
    have h1 : ∀ d ∈ m.divisors, ((((m : ℤ) * ArithmeticFunction.moebius d : ℤ) : ℚ) : ℂ) *
        (if c ^ (m / d) = 1 then (1 : ℂ) else 0) =
        if d ∣ m / o then (m : ℂ) * (ArithmeticFunction.moebius d : ℤ) else 0 := by
      intro d hd
      by_cases h : d ∣ m / o
      · have : c ^ (m / d) = 1 := (hiff d hd).mpr h
        simp [this, h]
      · have : ¬ c ^ (m / d) = 1 := fun h' => h ((hiff d hd).mp h')
        simp [this, h]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, hfilt, ← Finset.mul_sum]
    have h2 := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors (m / o))
    simp only [Int.cast_sum] at h2
    rw [h2]
    have e : theta C c = if o = m then (m : ℂ) else 0 := rfl
    have h3 : m / o = 1 ↔ o = m := by
      rw [Nat.div_eq_iff_eq_mul_left hopos hom]
      omega
    rw [e]
    by_cases h : o = m
    · rw [if_pos h, if_pos (h3.mpr h)]; simp
    · rw [if_neg h, if_neg (mt h3.mp h)]; simp
  rw [key]
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ ?_
  exact indicator_mem_charSpan ψ₁ hinj (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))

lemma mul_char_mem_charSpan {C : Type} [Group C] (φ : C →* ℂˣ) {f : C → ℂ}
    (hf : f ∈ charSpan C) : (fun c => (φ c : ℂ) * f c) ∈ charSpan C := by
  unfold charSpan at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ * ψ, by funext c; simp⟩
  | zero =>
    have : (fun c => (φ c : ℂ) * (0 : C → ℂ) c) = 0 := by funext c; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun c => (φ c : ℂ) * (x + y) c) =
        (fun c => (φ c : ℂ) * x c) + (fun c => (φ c : ℂ) * y c) := by
      funext c; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun c => (φ c : ℂ) * (a • x) c) = a • (fun c => (φ c : ℂ) * x c) := by
      funext c; simp [Rat.smul_def]; ring
    rw [this]; exact Submodule.smul_mem _ _ hx

lemma theta_mul_trace_mem {C : Type} [Group C] [Fintype C] [IsCyclic C] {n : ℕ}
    (A : C →* GL (Fin n) ℂ) :
    (fun c => theta C c * Matrix.trace ((A c : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) ∈
      charSpan C := by
  obtain ⟨ψ₁, hinj⟩ := exists_faithful_char C
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hm : 0 < Fintype.card C := Fintype.card_pos
  have hM : ((A g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ^ Fintype.card C = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one]
    simp
  obtain ⟨s, d, hs, h⟩ := trace_matrix_pow_eq_sum hm _ hM
  have hζ : IsPrimitiveRoot (ψ₁ g : ℂ) (Fintype.card C) := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf,
      orderOf_injective ψ₁ hinj g]
    rw [← Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hφ : ∀ l ∈ s, ∃ φ : C →* ℂˣ, (φ g : ℂ) = l := by
    intro l hl
    obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one (hs l hl)
    exact ⟨ψ₁ ^ i, by simp [hi]⟩
  choose! φ hφ using hφ
  have htr : (fun c => Matrix.trace ((A c : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) =
      ∑ l ∈ s, (d l : ℚ) • (fun c : C => (φ l c : ℂ)) := by
    funext c
    obtain ⟨k, rfl⟩ : c ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg c)
    have hk : ((A (g ^ k) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        ((A g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ^ k := by
      rw [map_pow, Units.val_pow_eq_pow_val]
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def]
    rw [hk, h k]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [map_pow, Units.val_pow_eq_pow_val, hφ l hl]
    simp
  have htr2 : (fun c => theta C c * Matrix.trace ((A c : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
      = ∑ l ∈ s, (d l : ℚ) • (fun c => (φ l c : ℂ) * theta C c) := by
    funext c
    have := congrFun htr c
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def] at this ⊢
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [htr2]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (mul_char_mem_charSpan (φ l) (theta_mem_charSpan ψ₁ hinj))

end Cyclic

section Induction

/-- The induced class function `Ind_H f` (the formula of `ArtinInduction`). -/
def indFun {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  fun g => (Nat.card H : ℂ)⁻¹ * ∑ x : G, if h : x * g * x⁻¹ ∈ H then f ⟨_, h⟩ else 0

lemma indFun_zero {G : Type} [Group G] [Fintype G] (H : Subgroup G) :
    indFun H (0 : H → ℂ) = 0 := by
  funext g; simp [indFun]

lemma indFun_add {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f f' : H → ℂ) :
    indFun H (f + f') = indFun H f + indFun H f' := by
  funext g
  simp only [indFun, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

lemma indFun_smul {G : Type} [Group G] [Fintype G] (H : Subgroup G) (a : ℚ) (f : H → ℂ) :
    indFun H (a • f) = a • indFun H f := by
  funext g
  simp only [indFun, Pi.smul_apply, Rat.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp; ring

lemma isTerm {G : Type} [Group G] (C : Subgroup G) [Fintype C] (χ : G → ℂ) (y : G) (h : y ∈ C) :
    (Nat.card C : ℂ)⁻¹ * (theta C ⟨y, h⟩ * χ y) = if orderOf y = Nat.card C then χ y else 0 := by
  have hc : (Nat.card C : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : theta C ⟨y, h⟩ = if orderOf y = Nat.card C then (Nat.card C : ℂ) else 0 := by
    unfold theta
    rw [Nat.card_eq_fintype_card, ← Subgroup.orderOf_coe]
  rw [this]
  split_ifs
  · field_simp
  · simp

lemma gen_iff {G : Type} [Group G] [Finite G] (C : Subgroup G) (y : G) :
    (y ∈ C ∧ orderOf y = Nat.card C) ↔ Subgroup.zpowers y = C := by
  constructor
  · rintro ⟨hy, ho⟩
    have hle : Subgroup.zpowers y ≤ C := (Subgroup.zpowers_le).mpr hy
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, ho]
  · rintro rfl
    exact ⟨Subgroup.mem_zpowers y, by rw [Nat.card_zpowers]⟩

lemma sum_indFun_theta {G : Type} [Group G] [Fintype G] [Fintype (Subgroup G)]
    (χ : G → ℂ) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (g : G) :
    ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => IsCyclic C),
      indFun C (fun c : C => theta C c * χ (c : G)) g = (Fintype.card G : ℂ) * χ g := by
  have h1 : ∀ C : Subgroup G, indFun C (fun c : C => theta C c * χ (c : G)) g =
      ∑ x : G, if Subgroup.zpowers (x * g * x⁻¹) = C then χ g else 0 := by
    intro C
    unfold indFun
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x * g * x⁻¹ ∈ C
    · rw [dif_pos h, isTerm C χ _ h, hχ]
      have e' : orderOf (x * g * x⁻¹) = Nat.card C ↔ Subgroup.zpowers (x * g * x⁻¹) = C := by
        rw [← gen_iff]; simp [h]
      rw [if_congr e' rfl rfl]
    · rw [dif_neg h]
      have : ¬ Subgroup.zpowers (x * g * x⁻¹) = C := fun hz => h ((gen_iff C _).mpr hz).1
      simp [this]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x : G, ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => IsCyclic C),
      (if Subgroup.zpowers (x * g * x⁻¹) = C then χ g else 0) = χ g := by
    intro x
    rw [Finset.sum_ite_eq, if_pos]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, inferInstance⟩
  simp [h2]

end Induction

/-- The `ℚ`-span of the induced characters from cyclic subgroups (as in `ArtinInduction`). -/
abbrev inducedSpan (G : Type) [Group G] [Fintype G] : Submodule ℚ (G → ℂ) :=
  Submodule.span ℚ {f : G → ℂ | ∃ (H : Subgroup G) (_ : IsCyclic H) (ψ : H →* ℂˣ),
    f = fun g => (Fintype.card H : ℂ)⁻¹ *
      ∑ x : G, if h : x * g * x⁻¹ ∈ H then (ψ ⟨_, h⟩ : ℂ) else 0}

lemma indFun_mem_inducedSpan {G : Type} [Group G] [Fintype G] (C : Subgroup G) [IsCyclic C]
    {f : C → ℂ} (hf : f ∈ charSpan C) : indFun C f ∈ inducedSpan G := by
  unfold charSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, rfl⟩ := hx
    refine Submodule.subset_span ⟨C, inferInstance, ψ, ?_⟩
    funext g
    simp [indFun, Nat.card_eq_fintype_card]
  | zero => rw [indFun_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [indFun_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [indFun_smul]; exact Submodule.smul_mem _ _ hx

/-- **Artin's induction theorem** (Milne, *CFT*, VIII, §10, p. 262), proved. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Artin's induction theorem)"]
theorem artinInduction : ArtinInduction := by
  refine ⟨fun G _ _ _ n ρ => ?_⟩
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  set χ : G → ℂ := fun g => Matrix.trace ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
    with hχdef
  have hcl : ∀ x g, χ (x * g * x⁻¹) = χ g := by
    intro x g
    simp only [hχdef, map_mul, map_inv, Units.val_mul]
    exact Matrix.trace_units_conj (ρ x) _
  have heq : χ = ((Fintype.card G : ℚ)⁻¹) • ∑ C ∈ Finset.univ.filter
      (fun C : Subgroup G => IsCyclic C), indFun C (fun c : C => theta C c * χ (c : G)) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, Rat.smul_def]
    rw [sum_indFun_theta χ hcl g]
    have : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    push_cast
    field_simp
  show χ ∈ inducedSpan G
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun C hC => ?_)
  have hcyc : IsCyclic C := (Finset.mem_filter.mp hC).2
  exact indFun_mem_inducedSpan C (theta_mul_trace_mem (ρ.comp C.subtype))

end NumberFieldKB.MilneCFT.Ch8
