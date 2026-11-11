import NumberFieldKB.MilneCFT.Ch6.RayClassBridge
import NumberFieldKB.MilneCFT.Ch5RayClassOrder
import NumberFieldKB.MilneCFT.Ch6.RegulatorMod
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.RayClass.Count.Asymptotic
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, VI, Proposition 2.8, unconditionally

$|S(x,k) - g_\mathfrak m x| \le C x^{1 - 1/d}$ for $x \ge 1$, from Tau Ceti's ray class ideal count
`TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub`
($S(x,k) = c_\mathfrak m x + O(x^{1-1/d})$ with $c_\mathfrak m = \rho_K h_\mathfrak m^{-1}\prod_{\mathfrak p\mid\mathfrak m_0}
(1 - N\mathfrak p^{-1})$, $\rho_K$ the residue of $\zeta_K$ at $1$) via the bridge `RayBridge.rayEquiv` of ray class
groups. The two constants agree (`rayResidue_eq_mainTerm`): with Theorem V.1.7 for $h_\mathfrak m$
(`theorem_1_7_card`) and the class number formula for $\rho_K$, this is
$\mathrm{reg}(\mathfrak m)\,w_K = \mathrm{reg}(K)\,(U : U_{\mathfrak m,1})\,w_\mathfrak m$ (`regulatorMod_mul`), the
index of the logarithmic image of $U_{\mathfrak m,1}$ in the unit lattice being $(U : U_{\mathfrak m,1}\mu_K)$.
-/

open NumberField IsDedekindDomain Asymptotics Filter NumberField.Units

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

open RayBridge

variable {K : Type} [Field K] [NumberField K]

/-- $S(x,k)$ is Tau Ceti's ray class ideal counting function. -/
theorem idealCount_eq (m : Modulus K) (k : RayClassGroup m) (x : ℝ) :
    idealCount m k x =
      TauCeti.GlobalNumberFields.rayClassIdealCountingFunction (toTC m) (rayEquiv m k) x := by
  rw [idealCount, TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def,
    ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun 𝔞 => ⟨⟨𝔞.1, mem_integralIdealsPrimeTo m 𝔞.2.1.1 𝔞.2.1.2⟩, ?_, 𝔞.2.2.2⟩
      invFun := fun I => ⟨I.1.1, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · obtain ⟨𝔞, h, hk, -⟩ := 𝔞
    rw [← rayEquiv_idealRayClass m 𝔞 h.1 h.2, hk]
  · obtain ⟨I, hI, hx⟩ := I
    have hc := TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_iff_sup_eq_top.mp
      (TauCeti.GlobalNumberFields.Modulus.mem_integralIdealsPrimeTo.mp I.2)
    refine ⟨hc, ?_, hx⟩
    apply (rayEquiv m).injective
    rw [rayEquiv_idealRayClass]
    exact hI

/-- $S(x, k)$ is nondecreasing in $x$. -/
theorem idealCount_mono (m : Modulus K) (k : RayClassGroup m) {x y : ℝ} (hxy : x ≤ y) :
    idealCount m k x ≤ idealCount m k y := by
  rw [idealCount_eq, idealCount_eq, TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def,
    TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def]
  exact Nat.card_le_card_of_injective (fun I => ⟨I.1, I.2.1, I.2.2.trans hxy⟩)
    (fun I J h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- The correction factor $\prod_{\mathfrak p \mid \mathfrak m_0}(1 - N\mathfrak p^{-1})$, over Tau Ceti's support or
over the prime factors of $\mathfrak m_0$. -/
theorem prod_support_eq (m : Modulus K) :
    ∏ v ∈ (toTC m).support, (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) =
      ((∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset,
        (1 - 1 / (Ideal.absNorm P : ℚ)) : ℚ) : ℝ) := by
  push_cast
  refine Finset.prod_bij (fun v _ => v.asIdeal) ?_ ?_ ?_ ?_
  · intro v hv
    rw [TauCeti.GlobalNumberFields.Modulus.mem_support_iff] at hv
    obtain ⟨q, hq, hvq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd
      (toTC m).finitePart_ne_zero v.irreducible hv
    rw [associated_iff_eq] at hvq
    rw [Multiset.mem_toFinset, hvq]
    exact hq
  · intro v _ w _ h
    exact HeightOneSpectrum.ext h
  · intro P hP
    rw [Multiset.mem_toFinset] at hP
    have hpr := UniqueFactorizationMonoid.prime_of_factor P hP
    refine ⟨⟨P, Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩, ?_, rfl⟩
    rw [TauCeti.GlobalNumberFields.Modulus.mem_support_iff]
    exact UniqueFactorizationMonoid.dvd_of_mem_factors hP
  · intro v _
    simp [one_div]

/-- **The constants agree**: $g_\mathfrak m$ is Tau Ceti's main term. -/
theorem rayResidue_eq_mainTerm (m : Modulus K) :
    rayResidue m = TauCeti.GlobalNumberFields.rayClassIdealMainTerm (toTC m) := by
  classical
  obtain ⟨hfin, hcard⟩ := theorem_1_7_card m
  have hcardTC : Nat.card (TauCeti.GlobalNumberFields.RayClassGroup (toTC m)) =
      Nat.card (RayClassGroup m) := Nat.card_congr (rayEquiv m).toEquiv.symm
  rw [TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq, hcardTC, prod_support_eq,
    dedekindZeta_residue_def]
  have hcardR : (Nat.card (RayClassGroup m) : ℝ) = ((Nat.card (RayClassGroup m) : ℚ) : ℝ) := by
    push_cast; rfl
  rw [hcardR, hcard]
  set P : ℚ := ∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset,
    (1 - 1 / (Ideal.absNorm P : ℚ))
  have hP : P ≠ 0 := by
    have h := TauCeti.GlobalNumberFields.rayClassIdealMainTerm_pos (toTC m)
    rw [TauCeti.GlobalNumberFields.rayClassIdealMainTerm_eq, prod_support_eq] at h
    intro h0
    rw [show (((∏ P ∈ (UniqueFactorizationMonoid.factors m.finite).toFinset,
      (1 - 1 / (Ideal.absNorm P : ℚ)) : ℚ)) : ℝ) = (P : ℝ) from rfl, h0] at h
    simp at h
  have hreg := regulatorMod_mul m
  have hw : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hwm : (rootsOfUnityMod m : ℝ) ≠ 0 := by
    have : 0 < rootsOfUnityMod m := by
      rw [rootsOfUnityMod]
      have : Finite {u : (𝓞 K)ˣ // u ∈ unitsMod m ∧ u ∈ torsion K} :=
        Finite.of_injective (fun u => (⟨u.1, u.2.2⟩ : torsion K))
          (fun u v h => Subtype.ext (by simpa using congrArg Subtype.val h))
      have : Nonempty {u : (𝓞 K)ˣ // u ∈ unitsMod m ∧ u ∈ torsion K} := ⟨⟨1, one_mem _, one_mem _⟩⟩
      exact Nat.card_pos
    exact_mod_cast this.ne'
  have hidx : ((congruenceSubgroup m).relIndex (unitsK K) : ℝ) ≠ 0 := by
    intro h0
    have h0' : (congruenceSubgroup m).relIndex (unitsK K) = 0 := by exact_mod_cast h0
    have := Nat.card_pos (α := RayClassGroup m)
    rw [h0'] at hcard
    simp at hcard
    omega
  have hh : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos K).ne'
  have hN : (Ideal.absNorm m.finite : ℝ) ≠ 0 := by
    have : Ideal.absNorm m.finite ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact m.finite_ne_bot
    exact_mod_cast this
  have hD : Real.sqrt |(discr K : ℝ)| ≠ 0 := by
    have : (discr K : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero K
    positivity
  have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP
  have hreg' : regulatorMod m = regulator K * ((congruenceSubgroup m).relIndex (unitsK K) : ℝ) *
      (rootsOfUnityMod m : ℝ) / (torsionOrder K : ℝ) := by
    rw [eq_div_iff hw, hreg]
  rw [rayResidue, modulusNorm, hreg']
  push_cast
  field_simp

/-- **Proposition 2.8** (Milne, *CFT*, VI, p. 189), unconditionally. -/
@[kb "milne2020cft" "Ch. VI, Prop. 2.8"]
theorem prop2_8 : Prop2_8 K := by
  refine ⟨fun m k => ?_⟩
  have hO := TauCeti.GlobalNumberFields.isBigO_rayClassIdealCountingFunction_sub (toTC m) (rayEquiv m k)
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp hC
  set e : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  have he : 0 ≤ e := by
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    simp only [e]
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  set X : ℝ := max x0 1
  set B : ℝ := (idealCount m k X : ℝ) + |rayResidue m| * X
  refine ⟨max C 0 + B, fun x hx => ?_⟩
  have hxe : 1 ≤ x ^ e := Real.one_le_rpow hx he
  have hB : 0 ≤ B := by positivity
  rcases le_or_gt x0 x with h | h
  · rw [rayResidue_eq_mainTerm, idealCount_eq]
    have := hx0 x h
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹))] at this
    have heq : x ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) = x ^ e := by simp [e, one_div]
    rw [heq] at this
    calc _ ≤ C * x ^ e := this
      _ ≤ max C 0 * x ^ e := by gcongr; exact le_max_left _ _
      _ ≤ (max C 0 + B) * x ^ e := by gcongr; linarith
  · have hxX : x ≤ X := le_trans h.le (le_max_left _ _)
    have hcnt : (idealCount m k x : ℝ) ≤ idealCount m k X := by exact_mod_cast idealCount_mono m k hxX
    have hx0' : (0 : ℝ) ≤ x := by linarith
    have h1 : |(idealCount m k x : ℝ) - rayResidue m * x| ≤ B := by
      calc _ ≤ |(idealCount m k x : ℝ)| + |rayResidue m * x| := abs_sub _ _
        _ = idealCount m k x + |rayResidue m| * x := by
          rw [abs_of_nonneg (Nat.cast_nonneg _), abs_mul, abs_of_nonneg hx0']
        _ ≤ B := by
          simp only [B]
          gcongr
    calc _ ≤ B := h1
      _ ≤ B * x ^ e := le_mul_of_one_le_right hB hxe
      _ ≤ (max C 0 + B) * x ^ e := by gcongr; linarith [le_max_right C 0]

end NumberFieldKB.MilneCFT.Ch6
