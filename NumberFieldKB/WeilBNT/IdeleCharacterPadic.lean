import NumberFieldKB.WeilBNT.PadicIdeleCharacters
import NumberFieldKB.WeilBNT.IdeleCharacterComplex
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Topology.Algebra.Group.Units

/-!
# Weil, *Basic Number Theory*, VII.§8, Corollary of Prop. 17, case (c): $\Gamma=K^\times$, $K$ a $p$-field

Notation as in `NumberFieldKB.WeilBNT.IdeleCharacterExtension` and `NumberFieldKB.WeilBNT.PadicIdeleCharacters`:
$k$ a number field (`K`), $P=P_\infty\cup S$, $\varphi:I(P)\to\Gamma$, and $\Gamma=L_w^\times$ with $L_w$ the completion
of a number field $L$ at a finite place $w$ above $p$.

* **`weil_VII_8_prop17_cor_padic`** (p. 137, case (c)): the extension $\omega$ of $\varphi\circ\mathrm{id}$ exists if
  and only if the $g_v$ and $\psi_v$ of Prop. 17 can be chosen with $\psi_v=1$ for every $v\in P$ at which $k_v$ is not
  a $p$-field: all infinite places, and the finite $v\in S$ with $v\nmid p$.

*Proof* (Weil's): as in case (b), replace $g_v$ by the kernel of $\psi_v$ wherever $k_v$ is not a $p$-field; that
kernel is open by the argument of Prop. 16 (a continuous morphism of an open subgroup of $k_v^\times$, $k_v$ not a
$p$-field, into $L_w^\times$ has an open kernel).
-/

open IsDedekindDomain NumberField Topology NumberFieldKB.MilneCFT nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]

theorem trivial_of_hom_onePlusPow (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∉ v.asIdeal)
    {m : ℕ} (hm : 1 ≤ m) (f : unitsOnePlusPow (K := K) v m →* (w.adicCompletion L)ˣ)
    (h : ∀ u, f u ∈ unitsOnePlusPow (K := L) w 1) : ∀ z, f z = 1 := by
  intro z
  have key : ∀ n : ℕ, Valued.v ((f z : w.adicCompletion L) - 1) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro n
    have hpn : ((p ^ n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
      rw [Nat.cast_pow]; exact fun h => hv (v.isPrime.mem_of_pow_mem _ h)
    obtain ⟨z', hz', hzz'⟩ := (weil_II_3_prop8_bijOn v hpn hm).surjOn z.2
    have hzz'' : (⟨z', hz'⟩ : unitsOnePlusPow (K := K) v m) ^ (p ^ n) = z :=
      Subtype.ext hzz'
    have : f z ∈ unitsOnePlusPow (K := L) w (n + 1) := by
      rw [← hzz'', map_pow]; exact weil_I_4_lemma5 w p hp n (h _)
    exact this.2
  have := eq_zero_of_forall_le_exp key
  have h0 : (f z : w.adicCompletion L) - 1 = 0 := (Valuation.zero_iff _).1 this
  exact Units.ext (sub_eq_zero.1 h0)

theorem isOpen_ker_padic_finite (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∉ v.asIdeal)
    (g : Subgroup (v.adicCompletion K)ˣ) (hg : IsOpen (g : Set (v.adicCompletion K)ˣ))
    (ψ : g →* (w.adicCompletion L)ˣ) (hψ : Continuous ψ) : IsOpen (ψ.ker : Set g) := by
  set f : g → v.adicCompletion K := fun u => ((u : (v.adicCompletion K)ˣ) : v.adicCompletion K) with hf
  have hfo : IsOpenMap f := (Units.isOpenEmbedding_val.isOpenMap).comp hg.isOpenEmbedding_subtypeVal.isOpenMap
  have hU : IsOpen (ψ ⁻¹' (unitsOnePlusPow (K := L) w 1 : Set (w.adicCompletion L)ˣ)) :=
    (isOpen_unitsOnePlusPow w 1).preimage hψ
  have hT : f '' (ψ ⁻¹' (unitsOnePlusPow (K := L) w 1 : Set (w.adicCompletion L)ˣ)) ∈
      𝓝 (1 : v.adicCompletion K) := by
    have := hfo.image_mem_nhds (x := (1 : g)) (hU.mem_nhds (by simp))
    simpa [hf] using this
  obtain ⟨n, hn⟩ := exists_valued_le_of_mem_nhds_one v hT
  have hex : ∀ z ∈ unitsOnePlusPow (K := K) v (n + 1), ∃ u : g, (u : (v.adicCompletion K)ˣ) = z ∧
      ψ u ∈ unitsOnePlusPow (K := L) w 1 := by
    intro z hz
    obtain ⟨u, hu, hue⟩ := hn (z : v.adicCompletion K) (hz.2.trans (WithZero.exp_le_exp.2 (by omega)))
    exact ⟨u, Units.ext hue, hu⟩
  have hsub : unitsOnePlusPow (K := K) v (n + 1) ≤ g := by
    intro z hz
    obtain ⟨u, hu, -⟩ := hex z hz
    rw [← hu]; exact u.2
  set F := ψ.comp (Subgroup.inclusion hsub) with hF
  have hFmem : ∀ z, F z ∈ unitsOnePlusPow (K := L) w 1 := by
    intro z
    obtain ⟨u, hu, hu'⟩ := hex z z.2
    have : u = Subgroup.inclusion hsub z := Subtype.ext hu
    rw [hF, MonoidHom.comp_apply, ← this]; exact hu'
  have hF1 := trivial_of_hom_onePlusPow w p hp v hv (m := n + 1) (by omega) F hFmem
  have hker : (unitsOnePlusPow (K := K) v (n + 1)).comap g.subtype ≤ ψ.ker := by
    intro u hu
    have := hF1 ⟨(u : (v.adicCompletion K)ˣ), hu⟩
    exact this
  exact Subgroup.isOpen_mono hker
    ((isOpen_unitsOnePlusPow v (n + 1)).preimage continuous_subtype_val)

theorem isOpen_ker_padic_infinite (w : HeightOneSpectrum (𝓞 L)) (v : InfinitePlace K)
    (g : Subgroup (v.Completion)ˣ) (hg : IsOpen (g : Set (v.Completion)ˣ))
    (ψ : g →* (w.adicCompletion L)ˣ) (hψ : Continuous ψ) : IsOpen (ψ.ker : Set g) := by
  have : LocallyConnectedSpace v.Completion := by
    by_cases hv : v.IsReal
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.1 hv)).toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace (v.Completion)ˣ := Units.isOpenEmbedding_val.locallyConnectedSpace
  have : LocallyConnectedSpace g := hg.isOpenEmbedding_subtypeVal.locallyConnectedSpace
  have hker : connectedComponent (1 : g) ⊆ ψ.ker := by
    intro z hz
    have hmem : ψ z ∈ connectedComponent (1 : (w.adicCompletion L)ˣ) := by
      have := hψ.image_connectedComponent_subset 1 ⟨z, hz, rfl⟩
      simpa using this
    have key : ∀ n : ℕ, ψ z ∈ unitsOnePlusPow (K := L) w (n + 1) := fun n =>
      (IsClopen.connectedComponent_subset
        ⟨Subgroup.isClosed_of_isOpen _ (isOpen_unitsOnePlusPow w (n + 1)), isOpen_unitsOnePlusPow w (n + 1)⟩
        (Subgroup.one_mem _)) hmem
    have h0 := eq_zero_of_forall_le_exp fun n => (key n).2
    exact Units.ext (sub_eq_zero.1 ((Valuation.zero_iff _).1 h0))
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (isOpen_connectedComponent.mem_nhds mem_connectedComponent) hker)

theorem eq_one_of_mem_map_ker {Γ : Type*} [Group Γ] {G : Type*} [Group G] {H : Subgroup G} (ψ : H →* Γ)
    {x : G} (hx : x ∈ ψ.ker.map H.subtype) (hxH : x ∈ H) : ψ ⟨x, hxH⟩ = 1 := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact hk

/-- **Weil, VII.§8, Corollary of Prop. 17, case (c)** (p. 137), number field case: for $\Gamma=L_w^\times$ a $p$-field,
the extension $\omega$ of $\varphi\circ\mathrm{id}$ exists if and only if open subgroups $g_v$ ($v\in P$, inside
$r_v^\times$ for $v$ finite) and morphisms $\psi_v$ can be found as in Prop. 17 with $\psi_v=1$ at the infinite places
and at the finite $v\in S$ with $v\nmid p$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Corollary of Prop. 17, case (c) (p. 137), number field case"]
theorem weil_VII_8_prop17_cor_padic (w : HeightOneSpectrum (𝓞 L)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 L) ∈ w.asIdeal) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* (w.adicCompletion L)ˣ) :
    (∃ ω : IdeleGroup (𝓞 K) K →* (w.adicCompletion L)ˣ, Continuous ω ∧
      (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧
      ∀ x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))),
        ∀ b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))), (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          ω x = φ b) ↔
    ∃ (gInf : ∀ v : InfinitePlace K, Subgroup (v.Completion)ˣ)
      (gFin : ∀ v : S, Subgroup ((v.1).adicCompletion K)ˣ),
      (∀ v, IsOpen (gInf v : Set (v.Completion)ˣ)) ∧ (∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) ∧
      (∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1) ∧
      ∃ ψFin : ∀ v, gFin v →* (w.adicCompletion L)ˣ, (∀ v, Continuous (ψFin v)) ∧
        (∀ v : S, (p : 𝓞 K) ∉ (v.1).asIdeal → ψFin v = 1) ∧
        Prop17Condition S gInf gFin φ (fun _ => 1) ψFin := by
  classical
  constructor
  · intro hω
    have hInf0 : ∀ v : InfinitePlace K, IsOpen ((⊤ : Subgroup (v.Completion)ˣ) : Set (v.Completion)ˣ) :=
      fun v => by rw [Subgroup.coe_top]; exact isOpen_univ
    have hFin0 : ∀ v : S, IsOpen ((unitsInt v.1 : Subgroup ((v.1).adicCompletion K)ˣ) :
        Set ((v.1).adicCompletion K)ˣ) := fun v => isOpen_unitsInt v.1
    have hU0 : ∀ v : S, ∀ u ∈ unitsInt v.1, Valued.v (u : (v.1).adicCompletion K) = 1 := fun v u hu => hu
    obtain ⟨ψInf, ψFin, hψInf, hψFin, hc⟩ := (weil_VII_8_prop17 hInf0 hFin0 hU0 φ).1 hω
    let gInf' : ∀ v : InfinitePlace K, Subgroup (v.Completion)ˣ := fun v =>
      (ψInf v).ker.map (⊤ : Subgroup (v.Completion)ˣ).subtype
    let gFin' : ∀ v : S, Subgroup ((v.1).adicCompletion K)ˣ := fun v =>
      if (p : 𝓞 K) ∉ (v.1).asIdeal then (ψFin v).ker.map (unitsInt v.1).subtype else unitsInt v.1
    have hle : ∀ v : S, gFin' v ≤ unitsInt v.1 := by
      intro v
      by_cases h : (p : 𝓞 K) ∉ (v.1).asIdeal
      · simp only [gFin', if_pos h]
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      · simp only [gFin', if_neg h]; exact le_rfl
    have hker : ∀ v : S, (p : 𝓞 K) ∉ (v.1).asIdeal → IsOpen ((ψFin v).ker : Set (unitsInt v.1)) := fun v h =>
      isOpen_ker_padic_finite w p hp v.1 h _ (hFin0 v) (ψFin v) (hψFin v)
    have hopFin : ∀ v : S, IsOpen (gFin' v : Set ((v.1).adicCompletion K)ˣ) := by
      intro v
      by_cases h : (p : 𝓞 K) ∉ (v.1).asIdeal
      · simp only [gFin', if_pos h]
        have := (hFin0 v).isOpenEmbedding_subtypeVal.isOpenMap _ (hker v h)
        rw [Subgroup.coe_map]
        exact this
      · simp only [gFin', if_neg h]; exact hFin0 v
    refine ⟨gInf', gFin', fun v => ?_, hopFin, fun v u hu => hle v hu, ?_⟩
    · have := (hInf0 v).isOpenEmbedding_subtypeVal.isOpenMap _
        (isOpen_ker_padic_infinite w v ⊤ (hInf0 v) (ψInf v) (hψInf v))
      show IsOpen (Subtype.val '' ((ψInf v).ker : Set (⊤ : Subgroup (v.Completion)ˣ)))
      exact this
    refine ⟨fun v => (ψFin v).comp (Subgroup.inclusion (hle v)), fun v => ?_, fun v hv => ?_, ?_⟩
    · exact (hψFin v).comp ((continuous_subtype_val).subtype_mk _)
    · refine MonoidHom.ext fun u => ?_
      have hu := u.2
      simp only [gFin', if_pos hv] at hu
      obtain ⟨k, hk, hku⟩ := hu
      have : Subgroup.inclusion (hle v) u = k := Subtype.ext hku.symm
      show (ψFin v) (Subgroup.inclusion (hle v) u) = 1
      rw [this]; exact hk
    · intro ξ hξ b hb
      have hξ0 : pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ) ∈
          gProd S (fun _ => (⊤ : Subgroup _)) (fun v : S => unitsInt (K := K) v.1) :=
        ⟨fun v => Subgroup.mem_top _, fun v => hle v (hξ.2 v)⟩
      have h := hc ξ hξ0 b hb
      rw [h, psiProd_apply, psiProd_apply]
      have h1 : ∀ v : InfinitePlace K, ψInf v (gProdInf v (⟨_, hξ0⟩ : gProd S (fun _ => (⊤ : Subgroup _))
          (fun v : S => unitsInt (K := K) v.1))) = 1 := by
        intro v
        exact eq_one_of_mem_map_ker (ψInf v) (hξ.1 v) (Subgroup.mem_top _)
      simp only [h1, MonoidHom.one_apply, Finset.prod_const_one, one_mul]
      rfl
  · rintro ⟨gInf, gFin, hInf, hFin, hFinU, ψFin, hψFin, -, hc⟩
    exact (weil_VII_8_prop17 hInf hFin hFinU φ).2
      ⟨fun _ => 1, ψFin, fun _ => continuous_const, hψFin, hc⟩

end NumberFieldKB.WeilBNT
