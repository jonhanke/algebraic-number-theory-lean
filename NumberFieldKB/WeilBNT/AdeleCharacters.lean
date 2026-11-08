import NumberFieldKB.WeilBNT.AdeleBoxes
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal

/-!
# Weil, *Basic Number Theory*, Chapter IV, §1, formula (2): characters of the adeles are products of local characters

$k$ is a number field and $k_{\mathbb A}$ Mathlib's adele ring. A character $\chi$ of the additive group of $k_{\mathbb A}$
(a continuous additive character with values in the circle) induces on each quasifactor $k_v$ a character $\chi_v$
($x\mapsto\chi$ of the adele with $x$ at $v$ and $0$ elsewhere). Weil (p. 60):

* $\chi_v$ is trivial on $r_v$ for almost all finite places $v$ (a character of the compact product $\prod_vr_v$ is
  trivial on almost all factors): `weil_IV_1_text2_trivial`;
* (2): $\chi(x)=\prod_v\chi_v(x_v)$ for every adele $x$, the product over all places, almost all factors being $1$:
  `weil_IV_1_text2_prod` (finite product over the infinite places times a `finprod` over the finite places).

Proof: by continuity there is a neighbourhood $U$ of $0$ with $\operatorname{Re}\chi>0$ on $U$; $U$ contains
$\{0\}_\infty\times\prod_{v\notin S}r_v$ for a finite set $S$ (with the other components small), and the image under $\chi$
of the subgroup $\prod_{v\notin S}r_v$ is a subgroup of the circle in the half-plane $\operatorname{Re}>0$, hence trivial.
Writing $x=x_S+x^S$ with $x^S\in\prod_{v\notin S}r_v$ gives (2).
-/

open IsDedekindDomain NumberField QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-- A point of the circle all of whose powers lie in the right half-plane is $1$. -/
theorem circle_eq_one_of_forall_pow_re_pos (z : Circle) (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) :
    z = 1 := by
  by_contra hz
  have hz1 : |Complex.arg (z : ℂ)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using h 1))
  have hexp : (z : ℂ) = Complex.exp ((Complex.arg (z : ℂ) : ℂ) * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
    exact this.symm
  set θ := Complex.arg (z : ℂ) with hθ
  have hθ0 : θ ≠ 0 := by
    intro h0
    apply hz
    apply Circle.ext
    rw [hexp, h0]
    simp
  have hα : 0 < |θ| := abs_pos.mpr hθ0
  have hpi := Real.pi_pos
  have hex : ∃ n : ℕ, Real.pi / 2 ≤ n * |θ| := by
    obtain ⟨n, hn⟩ := exists_nat_gt (Real.pi / 2 / |θ|)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hα] at hn
    exact hn.le
  classical
  set m := Nat.find hex with hm
  have hm1 : Real.pi / 2 ≤ m * |θ| := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm1
    simp at hm1
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hk1 : k * |θ| < Real.pi / 2 := not_le.mp (Nat.find_min hex (by omega))
  have hm2 : (m : ℝ) * |θ| < Real.pi := by
    rw [hk] at hm1 ⊢
    push_cast at hm1 ⊢
    nlinarith
  have hcos : Real.cos ((m : ℝ) * θ) ≤ 0 := by
    have : Real.cos ((m : ℝ) * θ) = Real.cos ((m : ℝ) * |θ|) := by
      rcases abs_choice θ with h' | h'
      · rw [h']
      · rw [h', mul_neg, Real.cos_neg]
    rw [this]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hm1 (by linarith)
  have hre : ((z ^ m : Circle) : ℂ).re = Real.cos ((m : ℝ) * θ) := by
    rw [Circle.coe_pow, hexp, ← Complex.exp_nat_mul]
    have : (m : ℂ) * ((θ : ℂ) * Complex.I) = ((m * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  have := h m
  rw [hre] at this
  linarith

/-- The restriction of a character of the adeles to the finite adeles. -/
def finiteChar (χ : AddChar (AdeleRing (𝓞 K) K) Circle) : AddChar (FiniteAdeleRing (𝓞 K) K) Circle :=
  χ.compAddMonoidHom (AddMonoidHom.inr _ _)

theorem finiteChar_apply (χ : AddChar (AdeleRing (𝓞 K) K) Circle) (y : FiniteAdeleRing (𝓞 K) K) :
    finiteChar χ y = χ ((0, y) : AdeleRing (𝓞 K) K) := rfl

theorem continuous_finiteChar {χ : AddChar (AdeleRing (𝓞 K) K) Circle} (hχ : Continuous χ) :
    Continuous (finiteChar χ) :=
  hχ.comp (continuous_const.prodMk continuous_id : Continuous fun y : FiniteAdeleRing (𝓞 K) K =>
    ((0, y) : AdeleRing (𝓞 K) K))

theorem addChar_map_finset_sum {A : Type*} [AddCommMonoid A] (ψ : AddChar A Circle) {ι : Type*}
    (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

open RestrictedProduct in
/-- A continuous additive character of the finite adeles is trivial on the adeles that vanish on a suitable finite set
of places and are integral everywhere. -/
theorem exists_finset_char_eq_one (ψ : AddChar (FiniteAdeleRing (𝓞 K) K) Circle) (hψ : Continuous ψ) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 K)), ∀ y : FiniteAdeleRing (𝓞 K) K,
      (∀ v ∈ F, y v = 0) → (∀ v, y v ∈ v.adicCompletionIntegers K) → ψ y = 1 := by
  classical
  have hΩ : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  let g : Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]_[⊤] → Circle :=
    fun y => ψ (RestrictedProduct.inclusion _ _ (le_top : Filter.cofinite ≤ ⊤) y)
  have hg : Continuous g := hψ.comp (RestrictedProduct.continuous_inclusion _)
  have hg0 : g 0 = 1 := by
    show ψ _ = 1
    have : RestrictedProduct.inclusion _ _ (le_top : Filter.cofinite ≤ ⊤)
        (0 : Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]_[⊤]) = 0 := rfl
    exact (congrArg ψ this).trans (AddChar.map_zero_eq_one ψ)
  have hW : g ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ nhds (0 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K]_[⊤]) :=
    hg.continuousAt.preimage_mem_nhds (hΩ.mem_nhds (by rw [hg0]; simp))
  rw [(RestrictedProduct.isEmbedding_coe_of_top).nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨V, hV, hVW⟩ := hW
  have h0 : (((0 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [v.adicCompletion K, v.adicCompletionIntegers K]_[⊤]) :
      Π v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)) = 0 := rfl
  rw [h0, nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIt⟩ := hV
  refine ⟨I, fun y hyI hyA => ?_⟩
  -- the circle-valued character on the subgroup is in the half-plane, for all multiples
  have key : ∀ n : ℕ, 0 < ((ψ (n • y) : Circle) : ℂ).re := by
    intro n
    let y' : Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]_[⊤] :=
      ⟨fun v => (n • y) v, Filter.Eventually.of_forall (fun v => by
        have : (n • y) v = n • y v := rfl
        show (n • y) v ∈ _
        rw [this]; exact nsmul_mem (hyA v) n)⟩
    have hy' : RestrictedProduct.inclusion _ _ (le_top : Filter.cofinite ≤ ⊤) y' = n • y := rfl
    have hmem : (y' : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) ∈ Set.pi (I : Set _) t := by
      intro v hv
      have : (n • y) v = n • y v := rfl
      show (n • y) v ∈ t v
      rw [this, hyI v hv, smul_zero]
      exact mem_of_mem_nhds (ht v)
    have := hVW (hIt hmem)
    simpa [g, hy'] using this
  apply circle_eq_one_of_forall_pow_re_pos
  intro n
  rw [← AddChar.map_nsmul_eq_pow]
  exact key n

/-- **Weil, IV.§1, text before (2)** (p. 60): a continuous additive character of $k_{\mathbb A}$ is trivial on $r_v$
(embedded as the adeles supported at $v$) for all but finitely many finite places $v$. -/
@[kb "weil1973bnt" "Ch. IV, §1, text p. 60 (characters of k_A are trivial on r_v for almost all v), number field case"]
theorem weil_IV_1_text2_trivial (χ : AddChar (AdeleRing (𝓞 K) K) Circle) (hχ : Continuous χ) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ x : v.adicCompletion K, Valued.v x ≤ 1 ∧
      χ ((0, singleAdele v x) : AdeleRing (𝓞 K) K) ≠ 1}.Finite := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_char_eq_one (K := K) (finiteChar χ) (continuous_finiteChar hχ)
  refine F.finite_toSet.subset ?_
  rintro v ⟨x, hx, hne⟩
  by_contra hvF
  apply hne
  refine hF (singleAdele v x) (fun u hu => singleAdele_apply_ne ?_ x) (fun u => ?_)
  · rintro rfl
    exact hvF hu
  · by_cases huv : u = v
    · subst huv
      rw [singleAdele_apply_self]
      exact hx
    · rw [singleAdele_apply_ne huv]
      exact zero_mem _

open Classical in
/-- **Weil, IV.§1, formula (2)** (p. 60): a continuous additive character of $k_{\mathbb A}$ is the product of the local
characters it induces on the quasifactors: $\chi(x)=\prod_w\chi_w(x_w)\cdot\prod_v\chi_v(x_v)$ (infinite places $w$, finite
places $v$; almost all factors of the second product are $1$). -/
@[kb "weil1973bnt" "Ch. IV, §1, formula (2) (p. 60), number field case"]
theorem weil_IV_1_text2_prod (χ : AddChar (AdeleRing (𝓞 K) K) Circle) (hχ : Continuous χ)
    (a : AdeleRing (𝓞 K) K) :
    χ a = (∏ w : InfinitePlace K, χ ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), χ ((0, singleAdele v (a.2 v)) : AdeleRing (𝓞 K) K) := by
  obtain ⟨F, hF⟩ := exists_finset_char_eq_one (K := K) (finiteChar χ) (continuous_finiteChar hχ)
  obtain ⟨S, hS⟩ := FiniteAdeleRing.exists_mem_box a.2
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ F with hT
  set b := a.2 with hb
  have hsplit : a = ((a.1, 0) : AdeleRing (𝓞 K) K) + ((0, b) : AdeleRing (𝓞 K) K) :=
    Prod.ext (by simp) (by simp [hb])
  have hsumeval : ∀ v, (∑ u ∈ T, singleAdele u (b u)) v = ∑ u ∈ T, (singleAdele u (b u)) v := fun v =>
    map_sum (RestrictedProduct.evalAddMonoidHom
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) v) (fun u => singleAdele u (b u)) T
  have hsum1 : ∀ v ∈ T, (∑ u ∈ T, singleAdele u (b u)) v = b v := by
    intro v hv
    rw [hsumeval, Finset.sum_eq_single v]
    · exact singleAdele_apply_self v _
    · intro u _ huv
      exact singleAdele_apply_ne (Ne.symm huv) _
    · intro h
      exact absurd hv h
  have hsum0 : ∀ v, v ∉ T → (∑ u ∈ T, singleAdele u (b u)) v = 0 := by
    intro v hv
    rw [hsumeval]
    refine Finset.sum_eq_zero (fun u hu => singleAdele_apply_ne ?_ _)
    rintro rfl
    exact hv hu
  have hψb : finiteChar χ b = ∏ v ∈ T, χ ((0, singleAdele v (b v)) : AdeleRing (𝓞 K) K) := by
    have h1 : finiteChar χ (b - ∑ u ∈ T, singleAdele u (b u)) = 1 := by
      apply hF
      · intro v hv
        have hvT : v ∈ T := Finset.mem_union_right _ hv
        show (b - ∑ u ∈ T, singleAdele u (b u)) v = 0
        have : (b - ∑ u ∈ T, singleAdele u (b u)) v = b v - (∑ u ∈ T, singleAdele u (b u)) v := rfl
        rw [this, hsum1 v hvT, sub_self]
      · intro v
        have : (b - ∑ u ∈ T, singleAdele u (b u)) v = b v - (∑ u ∈ T, singleAdele u (b u)) v := rfl
        rw [this]
        by_cases hv : v ∈ T
        · rw [hsum1 v hv, sub_self]; exact zero_mem _
        · rw [hsum0 v hv, sub_zero]
          exact hS v (fun h => hv (Finset.mem_union_left _ (by exact_mod_cast h)))
    have h2 : b = (b - ∑ u ∈ T, singleAdele u (b u)) + ∑ u ∈ T, singleAdele u (b u) := by
      abel
    conv_lhs => rw [h2]
    rw [AddChar.map_add_eq_mul, h1, one_mul]
    exact addChar_map_finset_sum (finiteChar χ) T _
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 K), χ ((0, singleAdele v (b v)) : AdeleRing (𝓞 K) K) =
      ∏ v ∈ T, χ ((0, singleAdele v (b v)) : AdeleRing (𝓞 K) K) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvT
    apply hv
    have hvS : v ∉ (S : Set (HeightOneSpectrum (𝓞 K))) := fun h => hvT (Finset.mem_coe.mpr (Finset.mem_union_left _ h))
    have hvF : v ∉ F := fun h => hvT (Finset.mem_coe.mpr (Finset.mem_union_right _ h))
    have := hF (singleAdele v (b v)) (fun u hu => singleAdele_apply_ne (fun h => hvF (by rw [← h]; exact hu)) _)
      (fun u => by
        by_cases huv : u = v
        · subst huv
          rw [singleAdele_apply_self]
          exact hS u hvS
        · rw [singleAdele_apply_ne huv]
          exact zero_mem _)
    exact this
  have hinf : χ ((a.1, 0) : AdeleRing (𝓞 K) K) =
      ∏ w : InfinitePlace K, χ ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K) := by
    have h1 : ((a.1, 0) : AdeleRing (𝓞 K) K) =
        ∑ w : InfinitePlace K, ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K) := by
      refine Prod.ext ?_ ?_
      · show a.1 = (∑ w : InfinitePlace K, ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K)).1
        rw [show (∑ w : InfinitePlace K, ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K)).1 =
          ∑ w : InfinitePlace K, Pi.single w (a.1 w) from
          map_sum (AddMonoidHom.fst _ _) _ _]
        exact (Finset.univ_sum_single a.1).symm
      · show (0 : FiniteAdeleRing (𝓞 K) K) = (∑ w : InfinitePlace K,
          ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K)).2
        rw [show (∑ w : InfinitePlace K, ((Pi.single w (a.1 w), 0) : AdeleRing (𝓞 K) K)).2 =
          ∑ w : InfinitePlace K, (0 : FiniteAdeleRing (𝓞 K) K) from
          map_sum (AddMonoidHom.snd _ _) _ _]
        simp
    conv_lhs => rw [h1]
    exact addChar_map_finset_sum χ _ _
  conv_lhs => rw [hsplit, AddChar.map_add_eq_mul, hinf]
  rw [hfin]
  congr 1

end NumberFieldKB.WeilBNT
