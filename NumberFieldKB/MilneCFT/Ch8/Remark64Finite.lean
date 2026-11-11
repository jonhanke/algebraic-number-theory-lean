import NumberFieldKB.MilneCFT.Ch8.Remark64
import NumberFieldKB.WeilBNT.GaloisCompletionsGalois
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Remark VIII.6.4: the local Galois data at the finite places

For a finite Galois extension $L/K$ of number fields and a finite place $v$ of $K$, a place $w \mid v$ of $L$ gives a
`LocalGaloisDatum K L K_v`: $E = L_w$ (a $K_v$-algebra through QuadFormsKB's `localRingHom`), $L \to L_w$ the
canonical map, $D = D_w = \{\sigma : \sigma w = w\}$ (the decomposition group, `galPlace σ w = w`) acting on $L_w$ by
continuous extension. The fixed field of $D_w$ is $K_v$ because $L_w/K_v$ is Galois with group $D_w$
(Weil, *Basic Number Theory*, III.§4, Cor. 4 of Thm. 4, `NumberFieldKB.WeilBNT.weil_III_4_cor4_galois`).

* `exists_place_above`: every finite place of $K$ has a place of $L$ above it (from Weil's degree count
  $\sum_{w \mid v} [L_w : K_v] = [L : K] \ge 1$, `sum_finrank_places`).
* `finiteDatum v w hw`: the datum; `finiteDatum_D`: its group is the decomposition group of $w$.
-/

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.WeilBNT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Every finite place of $K$ has a place of $L$ above it. -/
theorem exists_place_above (v : HeightOneSpectrum (𝓞 K)) :
    ∃ w : HeightOneSpectrum (𝓞 L), underPlace (k := K) w = v := by
  by_contra h
  push_neg at h
  have hsum := (WeilBNT.sum_finrank_places (k := K) (K := L) v).2
  haveI : IsEmpty (PlacesAbove (K := L) v) := ⟨fun w => h w.1 w.2⟩
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  exact (Module.finrank_pos (R := K) (M := L)).ne' hsum.symm

/-- The decomposition group $D_w = \{\sigma \in \operatorname{Gal}(L/K) : \sigma w = w\}$. -/
def decompGroup (w : HeightOneSpectrum (𝓞 L)) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | galPlace σ w = w}
  one_mem' := galPlace_one w
  mul_mem' {σ τ} hσ hτ := by
    change galPlace (σ * τ) w = w
    rw [galPlace_mul, hσ, hτ]
  inv_mem' {σ} hσ := by
    change galPlace σ⁻¹ w = w
    have h := galPlace_mul σ σ⁻¹ w
    rw [mul_inv_cancel, galPlace_one, hσ] at h
    exact h.symm

/-- **The local Galois datum at a finite place** $v$, from a place $w \mid v$ of $L$: $E = L_w$, the decomposition
group $D_w$ acting by continuous extension (Weil, III.§4, Cor. 4 of Thm. 4). -/
def finiteDatum [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : underPlace (k := K) w = v) : LocalGaloisDatum K L (v.adicCompletion K) :=
  letI := (localRingHom v w hw).toAlgebra
  let hG := weil_III_4_cor4_galois (k := K) (K := L) w v hw
  let ρ := Classical.choose hG.2
  have hρ := Classical.choose_spec hG.2
  { E := w.adicCompletion L
    instAlg := (localRingHom v w hw).toAlgebra
    emb := algebraMap L (w.adicCompletion L)
    emb_algebraMap := fun x => (localRingHom_algebraMap v w hw x).symm
    D := decompGroup w
    act :=
      { toFun := fun σ => ρ ⟨σ.1, σ.2⟩
        map_one' := by
          have h := hρ.2 ⟨1, galPlace_one w⟩ ⟨1, galPlace_one w⟩
          have h' : ρ ⟨1 * 1, by rw [galPlace_mul, galPlace_one, galPlace_one]⟩ = ρ ⟨1, galPlace_one w⟩ := by
            congr 2
          rw [h'] at h
          exact (mul_eq_left.mp h.symm)
        map_mul' := fun σ τ => hρ.2 ⟨σ.1, σ.2⟩ ⟨τ.1, τ.2⟩ }
    act_emb := fun σ x => hρ.1 ⟨σ.1, σ.2⟩ x
    fixed := by
      intro y hy
      haveI := (card_decomp_eq_finrank (k := K) (K := L) w v hw).1
      haveI := hG.1
      refine (IsGalois.mem_range_algebraMap_iff_fixed (F := v.adicCompletion K) y).mpr fun f => ?_
      obtain ⟨σ, rfl⟩ := ρ.surjective f
      exact hy ⟨σ.1, σ.2⟩ }

theorem finiteDatum_D [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hw : underPlace (k := K) w = v) : (finiteDatum v w hw).D = decompGroup w := rfl

end NumberFieldKB.MilneCFT.Ch8
