import NumberFieldKB.MilneCFT.Ch5Ideles
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Weil, *Basic Number Theory*, VII.§8, text p. 136: $G_P/G_P^0\cong I(P)$

$k$ is a number field (`K`), $k_{\mathbb A}^\times$ its idele group (`IdeleGroup`), and
$\mathrm{id}:k_{\mathbb A}^\times\to I(k)$, $z\mapsto\prod_v\mathfrak p_v^{\operatorname{ord}_v(z_v)}$ the ideal of an idele
(`ideleToIdeal`, Milne CFT V.4.1 in this library). $P$ is a finite set of places containing the infinite ones; it is
given by the finite set `S` of its finite places.

* `GP S`: the ideles with $z_v=1$ for $v\in P$ (Weil's $G_P$ of Prop. 15).
* `GP0 S`: Weil's $G_P^0=\prod_{v\notin P}r_v^\times$: the ideles of $G_P$ with $|z_v|_v=1$ for every $v\notin P$.
* `IP S`: the group $I(P)$ of fractional ideals prime to $P$ (no $\mathfrak p_v$, $v\in P$, occurs).
* **`weil_VII_8_text_p136`**: $\mathrm{id}$ maps $G_P$ onto $I(P)$ with kernel $G_P^0$;
  **`weil_VII_8_text_p136_equiv`**: so it induces an isomorphism $G_P/G_P^0\cong I(P)$.

*Proof.* `ideleToIdeal` is onto with kernel the ideles that are units at every finite place (`item_4_1`); an ideal
prime to $P$ is the ideal of an idele, and changing that idele to $1$ at the places of $P$ (where it is a unit) does
not change its ideal.
-/

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

open NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- Weil's $G_P$: the ideles with component $1$ at the infinite places and at the finite places of `S`. -/
def GP (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {z | (z : AdeleRing (𝓞 K) K).1 = 1 ∧ ∀ v ∈ S, ideleFinAt z v = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, fun v hv => ?_⟩
    · rw [Units.val_mul, Prod.fst_mul, ha1, hb1, one_mul]
    · rw [ideleFinAt_mul, ha2 v hv, hb2 v hv, one_mul]
  one_mem' := ⟨rfl, fun v _ => ideleFinAt_one v⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, fun v hv => ?_⟩
    · have h := congrArg Prod.fst a.mul_inv
      rw [Prod.fst_mul, ha1, one_mul, Prod.fst_one] at h
      exact h
    · rw [ideleFinAt_inv, ha2 v hv, inv_one]

variable (K) in
/-- Weil's $G_P^0=\prod_{v\notin P}r_v^\times$. -/
def GP0 (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {z | z ∈ GP K S ∧ ∀ v, Valued.v (ideleFinAt z v) = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v => ?_⟩
    rw [ideleFinAt_mul, map_mul, ha' v, hb' v, one_mul]
  one_mem' := ⟨one_mem _, fun v => by rw [ideleFinAt_one]; exact map_one _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun v => ?_⟩
    rw [ideleFinAt_inv, map_inv₀, ha' v, inv_one]

variable (K) in
/-- $I(P)$: the fractional ideals prime to $P$. -/
def IP (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v ∈ S, FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  mul_mem' := by
    intro a b ha hb v hv
    have h1 := ha v hv
    have h2 := hb v hv
    rw [Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _), h1, h2]
    rfl
  one_mem' := fun v _ => by
    rw [Units.val_one, FractionalIdeal.count_one]
  inv_mem' := by
    intro a ha v hv
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, ha v hv]
    rfl

/-- The exponent of the prime $v$ in the ideal of an idele vanishes exactly when the component at $v$ is a unit. -/
theorem count_ideleToIdeal_eq_zero_iff (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (ideleToIdeal K x : FractionalIdeal (𝓞 K)⁰ K) = 0 ↔
      Valued.v (ideleFinAt x v) = 1 := by
  have h := QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v
  have h' : FractionalIdeal.count K v (ideleToIdeal K x : FractionalIdeal (𝓞 K)⁰ K) =
      QuadFormsKB.Tamagawa.Measure.Weil.ordAt (Units.map (RingHom.snd (InfiniteAdeleRing K)
        (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v := h
  rw [h', QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff]
  rfl

/-- **Text p. 136.** $\mathrm{id}$ maps $G_P$ onto $I(P)$, with kernel $G_P^0$. -/
@[kb "weil1973bnt" "Ch. VII, §8, text p. 136 (id maps G_P onto I(P) with kernel G_P⁰)"]
theorem weil_VII_8_text_p136 (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (GP K S).map (ideleToIdeal K) = IP K S ∧ ∀ z ∈ GP K S, ideleToIdeal K z = 1 ↔ z ∈ GP0 K S := by
  classical
  refine ⟨?_, fun z hz => ?_⟩
  · ext J
    constructor
    · rintro ⟨x, ⟨_, hx2⟩, rfl⟩ v hv
      rw [count_ideleToIdeal_eq_zero_iff, hx2 v hv, map_one]
    · intro hJ
      obtain ⟨z₀, hz₀⟩ := QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_surjective (F := K) J
      let z : (FiniteAdeleRing (𝓞 K) K)ˣ := z₀ * ∏ v ∈ S, QuadFormsKB.Tamagawa.Measure.Weil.mulSingleAt v
        ((QuadFormsKB.Tamagawa.Measure.Weil.unitAt z₀ v)⁻¹)
      have hz : ∀ v', unitAtHom v' z = unitAtHom v' z₀ * ∏ v ∈ S, unitAtHom v'
          (QuadFormsKB.Tamagawa.Measure.Weil.mulSingleAt v ((QuadFormsKB.Tamagawa.Measure.Weil.unitAt z₀ v)⁻¹)) := by
        intro v'
        simp only [z, map_mul, map_prod]
      have hin : ∀ v' ∈ S, unitAtHom v' z = 1 := by
        intro v' hv'
        rw [hz, Finset.prod_eq_single_of_mem v' hv']
        · show _ * QuadFormsKB.Tamagawa.Measure.Weil.unitAt
            (QuadFormsKB.Tamagawa.Measure.Weil.mulSingleAt v' _) v' = 1
          rw [QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mulSingleAt]
          exact mul_inv_cancel _
        · intro b _ hb
          exact QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mulSingleAt_of_ne (Ne.symm hb) _
      have hout : ∀ v' ∉ S, unitAtHom v' z = unitAtHom v' z₀ := by
        intro v' hv'
        rw [hz, Finset.prod_eq_one, mul_one]
        intro v hv
        exact QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mulSingleAt_of_ne (fun h => hv' (by rw [h]; exact hv)) _
      have hid : QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal K z = J := by
        refine QuadFormsKB.Tamagawa.Measure.Weil.fracIdeal_ext_count fun v' => ?_
        rw [QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal, ← hz₀,
          QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal]
        by_cases hv' : v' ∈ S
        · have h0 : QuadFormsKB.Tamagawa.Measure.Weil.ordAt z₀ v' = 0 := by
            rw [← QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal, hz₀]
            exact hJ v' hv'
          rw [h0, QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff]
          have := congrArg (fun u : (v'.adicCompletion K)ˣ => (u : v'.adicCompletion K)) (hin v' hv')
          simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk, QuadFormsKB.Tamagawa.Measure.Weil.unitAt_val,
            Units.val_one] at this
          rw [this, map_one]
        · have := congrArg (fun u : (v'.adicCompletion K)ˣ => (u : v'.adicCompletion K)) (hout v' hv')
          simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk,
            QuadFormsKB.Tamagawa.Measure.Weil.unitAt_val] at this
          simp only [QuadFormsKB.Tamagawa.Measure.Weil.ordAt, this]
      refine ⟨Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) z,
        ⟨rfl, fun v hv => ?_⟩, ?_⟩
      · have := congrArg (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) (hin v hv)
        simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk, QuadFormsKB.Tamagawa.Measure.Weil.unitAt_val,
          Units.val_one] at this
        exact this
      · rw [← hid]
        rfl
  · rw [(item_4_1 (K := K)).2 z]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩

/-- **Text p. 136.** $G_P/G_P^0\cong I(P)$. -/
@[kb "weil1973bnt" "Ch. VII, §8, text p. 136 (G_P / G_P⁰ ≅ I(P))"]
theorem weil_VII_8_text_p136_equiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty ((GP K S) ⧸ (GP0 K S).subgroupOf (GP K S) ≃* IP K S) := by
  obtain ⟨h1, h2⟩ := weil_VII_8_text_p136 (K := K) S
  let f : GP K S →* IP K S :=
    ((ideleToIdeal K).comp (GP K S).subtype).codRestrict (IP K S) fun x => by
      rw [← h1]
      exact ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    intro J
    have : (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ (GP K S).map (ideleToIdeal K) := by rw [h1]; exact J.2
    obtain ⟨x, hx, hxJ⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxJ⟩
  have hker : f.ker = (GP0 K S).subgroupOf (GP K S) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← h2 x x.2]
    exact Subtype.ext_iff
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end NumberFieldKB.WeilBNT
