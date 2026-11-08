import NumberFieldKB.WeilBNT.IdeleCharacterExtension

/-!
# Weil, *Basic Number Theory*, VII.§8, Corollary of Prop. 17, case (b): $\Gamma=\mathbb C^\times$

Notation as in `NumberFieldKB.WeilBNT.IdeleCharacterExtension`.

* **VII.§3, Lemmas 2–3, in the form used here**: $\mathbb C^\times$ has no small subgroups
  (`noSmallSubgroups_complexUnits`).
* **VII.§3, Lemma 4, first assertion, for open subgroups of $k_v^\times$** ($v$ finite): a morphism into
  $\mathbb C^\times$ is trivial on an open subgroup, i.e. has an open kernel (`isOpen_ker_of_complexUnits`); the
  subgroups $1+\mathfrak p_v^n$ form a basis of neighbourhoods of $1$.
* **Corollary of Prop. 17, case (b)** (p. 137): for $\Gamma=\mathbb C^\times$ the extension $\omega$ exists if and only
  if the $g_v$ and $\psi_v$ of Prop. 17 can be chosen with $\psi_v=1$ for every finite $v\in P$
  (`weil_VII_8_prop17_cor_complex`).

*Proof* (Weil's): replace, for each finite $v\in P$, $g_v$ by the kernel of $\psi_v$, an open subgroup of $g_v$.
-/

open IsDedekindDomain NumberField Filter Topology NumberFieldKB.MilneCFT nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-- **Weil, VII.§3, Lemmas 2–3** (the form used in VII.§8): $\mathbb C^\times$ has no small subgroups. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemmas 2-3 (C^x has no small subgroups)"]
theorem noSmallSubgroups_complexUnits : NoSmallSubgroups ℂˣ := by
  refine ⟨{z : ℂˣ | 1 / 2 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 2 ∧ 0 < (z : ℂ).re}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp; norm_num)
    have hc : Continuous fun z : ℂˣ => (z : ℂ) := Units.continuous_val
    exact (isOpen_lt continuous_const hc.norm).inter
      ((isOpen_lt hc.norm continuous_const).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hc)))
  · intro H hH
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    have hz1' : z ≠ 1 := hz1
    -- norms of elements of `H` are at most `1`
    have hle : ∀ w ∈ H, ‖(w : ℂ)‖ ≤ 1 := by
      intro w hw
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hlt
      have := (hH (H.pow_mem hw n)).2.1
      rw [Units.val_pow_eq_pow_val, norm_pow] at this
      linarith
    have h1 := hle z hz
    have h2 := hle z⁻¹ (H.inv_mem hz)
    rw [Units.val_inv_eq_inv_val, norm_inv] at h2
    have hn0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
    have hnorm : ‖(z : ℂ)‖ = 1 := by
      have : 1 ≤ ‖(z : ℂ)‖ := by
        by_contra hlt
        push Not at hlt
        have := (inv_lt_inv₀ (by norm_num) hn0).2 hlt
        rw [inv_one] at this
        linarith
      linarith
    set θ := Complex.arg (z : ℂ) with hθ
    have hzexp : (z : ℂ) = Complex.exp (θ * Complex.I) := by
      have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
      rw [hnorm, Complex.ofReal_one, one_mul] at this
      exact this.symm
    have hθ0 : θ ≠ 0 := by
      intro h0
      apply hz1'
      apply Units.ext
      rw [hzexp, h0]; simp
    have hpos : 0 < |θ| := abs_pos.2 hθ0
    have hex : ∃ k : ℕ, Real.pi / 2 ≤ k * |θ| := by
      obtain ⟨k, hk⟩ := Archimedean.arch (Real.pi / 2) hpos
      exact ⟨k, by simpa [nsmul_eq_mul] using hk⟩
    classical
    set k := Nat.find hex with hk
    have hkspec : Real.pi / 2 ≤ k * |θ| := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h
      rw [h] at hkspec
      simp at hkspec
      linarith [Real.pi_pos]
    have hkm : ¬ (Real.pi / 2 ≤ ((k - 1 : ℕ) : ℝ) * |θ|) := Nat.find_min hex (by omega)
    have hlt : ((k : ℝ) - 1) * |θ| < Real.pi / 2 := by
      push Not at hkm
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at hkm
    have hre : 0 < (z : ℂ).re := (hH hz).2.2
    have hθlt : |θ| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    have hzk : (z ^ k) ∈ H := H.pow_mem hz k
    have hre2 : 0 < ((z ^ k : ℂˣ) : ℂ).re := (hH hzk).2.2
    rw [Units.val_pow_eq_pow_val, hzexp, ← Complex.exp_nat_mul,
      show (k : ℂ) * (θ * Complex.I) = ((k * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re] at hre2
    have hcos : Real.cos (k * θ) ≤ 0 := by
      have : Real.cos (k * θ) = Real.cos (k * |θ|) := by
        rcases abs_choice θ with h | h
        · rw [h]
        · rw [h, mul_neg, Real.cos_neg]
      rw [this]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le hkspec
      nlinarith [Real.pi_pos]
    linarith

/-- **Weil, VII.§3, Lemma 4, first assertion** (for open subgroups of $k_v^\times$, $v$ finite): a morphism into
$\mathbb C^\times$ has an open kernel. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemma 4, first assertion (open subgroups of k_v^x, v finite)"]
theorem isOpen_ker_of_complexUnits (v : HeightOneSpectrum (𝓞 K)) (g : Subgroup (v.adicCompletion K)ˣ)
    (hg : IsOpen (g : Set (v.adicCompletion K)ˣ)) (ψ : g →* ℂˣ) (hψ : Continuous ψ) :
    IsOpen (ψ.ker : Set g) := by
  obtain ⟨U, hUn, hU⟩ := noSmallSubgroups_complexUnits
  set f : g → v.adicCompletion K := fun u => ((u : (v.adicCompletion K)ˣ) : v.adicCompletion K) with hf
  have hfo : IsOpenMap f := (Units.isOpenEmbedding_val.isOpenMap).comp hg.isOpenEmbedding_subtypeVal.isOpenMap
  have hfinj : Function.Injective f := fun a b h => Subtype.ext (Units.ext h)
  have hT : f '' (ψ ⁻¹' U) ∈ 𝓝 (1 : v.adicCompletion K) := by
    have := hfo.image_mem_nhds (x := (1 : g)) (hψ.continuousAt.preimage_mem_nhds (by simpa using hUn))
    simpa [hf] using this
  obtain ⟨n, hn⟩ := exists_valued_le_of_mem_nhds_one v hT
  set m : ℕ := n + 1
  have hm : (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  -- the elements of `g` close to `1`
  have hu1 : ∀ u : g, Valued.v (f u - 1) ≤ WithZero.exp (-(m : ℤ)) → Valued.v (f u) = 1 := by
    intro u hu
    have hu' : Valued.v (f u - 1) < 1 := lt_of_le_of_lt hu hm
    have hle : Valued.v (f u) ≤ 1 := by
      have : f u = (f u - 1) + 1 := by ring
      rw [this]
      exact Valuation.map_add_le _ hu'.le (by simp)
    refine le_antisymm hle ?_
    by_contra hlt
    push Not at hlt
    have : (1 : v.adicCompletion K) = f u - (f u - 1) := by ring
    have h1 : Valued.v (1 : v.adicCompletion K) ≤ max (Valued.v (f u)) (Valued.v (f u - 1)) := by
      conv_lhs => rw [this]
      exact Valuation.map_sub _ _ _
    rw [map_one] at h1
    rcases le_max_iff.1 h1 with h | h
    · exact absurd h (not_le.2 hlt)
    · exact absurd h (not_le.2 hu')
  let H : Subgroup g :=
    { carrier := {u | Valued.v (f u - 1) ≤ WithZero.exp (-(m : ℤ))}
      one_mem' := by simp [hf]
      mul_mem' := by
        intro a b ha hb
        have hva := hu1 a ha
        have : f (a * b) - 1 = f a * (f b - 1) + (f a - 1) := by simp [hf]; ring
        show Valued.v (f (a * b) - 1) ≤ _
        rw [this]
        refine Valuation.map_add_le _ ?_ ha
        rw [map_mul, hva, one_mul]; exact hb
      inv_mem' := by
        intro a ha
        have hva := hu1 a ha
        have hinv : f a⁻¹ = (f a)⁻¹ := by simp [hf]
        have : f a⁻¹ - 1 = -((f a)⁻¹ * (f a - 1)) := by
          rw [hinv]
          have : f a ≠ 0 := by intro h0; rw [h0] at hva; simp at hva
          field_simp; ring
        show Valued.v (f a⁻¹ - 1) ≤ _
        rw [this, Valuation.map_neg, map_mul, map_inv₀, hva, inv_one, one_mul]; exact ha }
  have hHo : IsOpen (H : Set g) := by
    have : (H : Set g) = (fun u : g => f u) ⁻¹' {z : v.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(m : ℤ))} :=
      rfl
    rw [this]
    exact (isOpen_valued_sub_one_le v (m : ℤ)).preimage (Units.continuous_val.comp continuous_subtype_val)
  have hHk : H ≤ ψ.ker := by
    have hsub : (H.map ψ : Set ℂˣ) ⊆ U := by
      rintro _ ⟨u, hu, rfl⟩
      have : f u ∈ f '' (ψ ⁻¹' U) := hn (f u) (le_trans hu (WithZero.exp_le_exp.2 (by omega)))
      obtain ⟨u', hu', he⟩ := this
      rw [← hfinj he]; exact hu'
    have := hU _ hsub
    intro u hu
    have : ψ u ∈ H.map ψ := ⟨u, hu, rfl⟩
    simp_all
  exact Subgroup.isOpen_mono hHk hHo

/-- **Weil, VII.§8, Corollary of Prop. 17, case (b)** (p. 137), number field case: for $\Gamma=\mathbb C^\times$, the
extension $\omega$ of $\varphi\circ\mathrm{id}$ exists if and only if open subgroups $g_v$ ($v\in P$, inside
$r_v^\times$ for $v$ finite) and morphisms $\psi_v$ can be found as in Prop. 17 with $\psi_v=1$ for the finite
$v\in P$. -/
@[kb "weil1973bnt" "Ch. VII, §8, Corollary of Prop. 17, case (b) (p. 137), number field case"]
theorem weil_VII_8_prop17_cor_complex (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))) →* ℂˣ) :
    (∃ ω : IdeleGroup (𝓞 K) K →* ℂˣ, Continuous ω ∧ (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧
      ∀ x ∈ idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))),
        ∀ b : sIdeals (S : Set (HeightOneSpectrum (𝓞 K))), (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          ω x = φ b) ↔
    ∃ (gInf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) (gFin : ∀ v : S, Subgroup ((v.1).adicCompletion K)ˣ),
      (∀ w, IsOpen (gInf w : Set (w.Completion)ˣ)) ∧ (∀ v, IsOpen (gFin v : Set ((v.1).adicCompletion K)ˣ)) ∧
      (∀ v, ∀ u ∈ gFin v, Valued.v (u : (v.1).adicCompletion K) = 1) ∧
      ∃ ψInf : ∀ w, gInf w →* ℂˣ, (∀ w, Continuous (ψInf w)) ∧
        Prop17Condition S gInf gFin φ ψInf (fun _ => 1) := by
  constructor
  · intro hω
    have hInf0 : ∀ w : InfinitePlace K, IsOpen ((⊤ : Subgroup (w.Completion)ˣ) : Set (w.Completion)ˣ) :=
      fun w => by rw [Subgroup.coe_top]; exact isOpen_univ
    have hFin0 : ∀ v : S, IsOpen ((unitsInt v.1 : Subgroup ((v.1).adicCompletion K)ˣ) :
        Set ((v.1).adicCompletion K)ˣ) := fun v => isOpen_unitsInt v.1
    have hU0 : ∀ v : S, ∀ u ∈ unitsInt v.1, Valued.v (u : (v.1).adicCompletion K) = 1 := fun v u hu => hu
    obtain ⟨ψInf, ψFin, hψInf, hψFin, hc⟩ := (weil_VII_8_prop17 hInf0 hFin0 hU0 φ).1 hω
    have hker : ∀ v : S, IsOpen ((ψFin v).ker : Set (unitsInt v.1)) := fun v =>
      isOpen_ker_of_complexUnits v.1 _ (hFin0 v) (ψFin v) (hψFin v)
    refine ⟨fun _ => ⊤, fun v => (ψFin v).ker.map (unitsInt v.1).subtype, hInf0, fun v => ?_, fun v u hu => ?_,
      ψInf, hψInf, ?_⟩
    · have := (hFin0 v).isOpenEmbedding_subtypeVal.isOpenMap _ (hker v)
      rw [Subgroup.coe_map]
      exact this
    · obtain ⟨x, -, rfl⟩ := hu
      exact x.2
    · intro ξ hξ b hb
      have hξ0 : pproj S (IdeleGroup.unitEmbedding (𝓞 K) K ξ) ∈
          gProd S (fun _ => (⊤ : Subgroup _)) (fun v : S => unitsInt (K := K) v.1) := by
        refine ⟨hξ.1, fun v => ?_⟩
        obtain ⟨x, -, hx⟩ := hξ.2 v
        rw [← hx]; exact x.2
      have h := hc ξ hξ0 b hb
      rw [h, psiProd_apply, psiProd_apply]
      congr 1
      refine (Finset.prod_eq_one fun v _ => ?_).trans (Finset.prod_const_one).symm
      obtain ⟨x, hx, hxe⟩ := hξ.2 v
      have : gProdFin v (⟨_, hξ0⟩ : gProd S (fun _ => (⊤ : Subgroup _)) (fun v : S => unitsInt (K := K) v.1)) = x :=
        Subtype.ext hxe.symm
      rw [this]; exact hx
  · rintro ⟨gInf, gFin, hInf, hFin, hFinU, ψInf, hψInf, hc⟩
    exact (weil_VII_8_prop17 hInf hFin hFinU φ).2
      ⟨ψInf, fun _ => 1, hψInf, fun _ => continuous_const, hc⟩

end NumberFieldKB.WeilBNT
