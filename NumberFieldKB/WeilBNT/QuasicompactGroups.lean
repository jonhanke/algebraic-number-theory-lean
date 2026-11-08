import NumberFieldKB.GlobalZeta.FunctionalEquation
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Weil, *Basic Number Theory*, VII.§3, Def. 5 and Def. 6: quasicompact groups and principal quasicharacters

* `IsQuasicompactGroup`: **Def. 5.** A commutative topological group $G$ is *quasicompact* if it is the direct
  product (as a topological group) of a compact subgroup $G_1$ and a closed subgroup $N$ isomorphic to $\mathbb R$ or
  to $\mathbb Z$. A *quasicharacter* is a continuous morphism $G\to\mathbb C^\times$ (`Quasicharacter`).
* **`weil_VII_3_def5_maximal`**: in such a decomposition, $G_1$ is the largest compact subgroup of $G$ (every compact
  subgroup is contained in it), so it depends only on $G$; this is what makes Def. 6 meaningful.
* `IsPrincipalQuasicharacter`: **Def. 6.** A quasicharacter is *principal* if it is trivial on the maximal compact
  subgroup, i.e. on every compact subgroup (`isPrincipal_iff_of_decomposition`: equivalently on $G_1$).
* **`weil_VII_3_def6_ideleClass`**: for the idele class group $C_k$ of a number field (where $C_k^1$ is compact), a
  Hecke character is principal if and only if it is $|\cdot|^s$ for some $s\in\mathbb C$ (`HeckeCharacter.normPow`).

*Proof.* The image of a compact subgroup $H$ under the projection $G\to N$ is a compact subgroup of $\mathbb R$ or
$\mathbb Z$, hence trivial. For $C_k$: a principal character is trivial on the compact group $C_k^1$, hence a power of
the norm (`exists_eq_normPow_of_ideleOne`); conversely the norm maps a compact subgroup onto a compact subgroup of
$\mathbb R_{>0}$, which is $\{1\}$, so it lies in $C_k^1$ where $|\cdot|^s$ is $1$.
-/

open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

section General

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Def. 5.** $G$ is quasicompact: $G=G_1\times N$ as topological groups, $G_1$ compact, $N$ isomorphic to
$\mathbb R$ or $\mathbb Z$. -/
def IsQuasicompactGroup : Prop :=
  ∃ (G₁ N : Subgroup G), IsCompact (G₁ : Set G) ∧
    (∃ e : (G₁ × N) ≃ₜ* G, ∀ x, e x = (x.1 : G) * x.2) ∧
    (Nonempty (N ≃ₜ* Multiplicative ℝ) ∨ Nonempty (N ≃ₜ* Multiplicative ℤ))

/-- **Def. 5.** A quasicharacter of $G$: a continuous morphism into $\mathbb C^\times$. -/
abbrev Quasicharacter := ContinuousMonoidHom G ℂˣ

variable {G}

/-- **Def. 6.** A quasicharacter is principal if it is trivial on the maximal compact subgroup, i.e. on every
compact subgroup. -/
def IsPrincipalQuasicharacter (ω : Quasicharacter G) : Prop :=
  ∀ H : Subgroup G, IsCompact (H : Set G) → ∀ h ∈ H, ω h = 1

/-- A compact subgroup of $\mathbb R$ (written multiplicatively) is trivial. -/
theorem eq_one_of_isCompact_real {H : Subgroup (Multiplicative ℝ)} (hH : IsCompact (H : Set (Multiplicative ℝ)))
    {x : Multiplicative ℝ} (hx : x ∈ H) : x = 1 := by
  by_contra hne
  have ha : Multiplicative.toAdd x ≠ 0 := fun h => hne (by simpa using h)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hH.image continuous_toAdd).isBounded
  obtain ⟨n, hn⟩ := Archimedean.arch (C + 1) (abs_pos.mpr ha)
  have := hC _ ⟨x ^ n, H.pow_mem hx n, rfl⟩
  rw [toAdd_pow, Real.norm_eq_abs, nsmul_eq_mul, abs_mul, Nat.abs_cast] at this
  rw [nsmul_eq_mul] at hn
  linarith

/-- A compact subgroup of $\mathbb Z$ (written multiplicatively) is trivial. -/
theorem eq_one_of_isCompact_int {H : Subgroup (Multiplicative ℤ)} (hH : IsCompact (H : Set (Multiplicative ℤ)))
    {x : Multiplicative ℤ} (hx : x ∈ H) : x = 1 := by
  by_contra hne
  have ha : Multiplicative.toAdd x ≠ 0 := fun h => hne (by simpa using h)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hH.image continuous_toAdd).isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC _ ⟨x ^ n, H.pow_mem hx n, rfl⟩
  rw [toAdd_pow] at h
  have h1 : (n : ℝ) ≤ ‖n • Multiplicative.toAdd x‖ := by
    rw [Int.norm_eq_abs, nsmul_eq_mul]
    push_cast
    rw [abs_mul, Nat.abs_cast]
    have h3 : (1 : ℝ) ≤ |((Multiplicative.toAdd x : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ha
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

/-- A continuous morphism into a group whose compact subgroups are trivial kills every compact subgroup. -/
theorem map_eq_one_of_isCompact {M : Type*} [Group M] [TopologicalSpace M]
    (hM : ∀ K : Subgroup M, IsCompact (K : Set M) → ∀ x ∈ K, x = 1)
    {A : Type*} [Group A] [TopologicalSpace A] (φ : A →* M) (hφ : Continuous φ)
    {H : Subgroup A} (hH : IsCompact (H : Set A)) {h : A} (hh : h ∈ H) : φ h = 1 :=
  hM (H.map φ) (by rw [Subgroup.coe_map]; exact hH.image hφ) _ ⟨h, hh, rfl⟩

omit [IsTopologicalGroup G] in
/-- Compact subgroups of $\mathbb R$ or $\mathbb Z$, via an isomorphism, are trivial in $N$; so a compact subgroup of a
product $G_1\times N$ lies in $G_1$. -/
theorem le_of_isCompact_aux {G₁ N : Subgroup G} (e : (G₁ × N) ≃ₜ* G) (he : ∀ x, e x = (x.1 : G) * x.2)
    {M : Type*} [Group M] [TopologicalSpace M]
    (hM : ∀ K : Subgroup M, IsCompact (K : Set M) → ∀ x ∈ K, x = 1) (f : N ≃ₜ* M)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) : H ≤ G₁ := by
  intro h hh
  let φ : G →* M := (f : N →* M).comp ((MonoidHom.snd G₁ N).comp (e.symm : G →* G₁ × N))
  have hφ : Continuous φ := f.continuous.comp (continuous_snd.comp e.symm.continuous)
  have h1 : φ h = 1 := map_eq_one_of_isCompact hM φ hφ hH hh
  have h2 : (e.symm h).2 = 1 := by
    have : f (e.symm h).2 = 1 := h1
    exact (map_eq_one_iff f f.injective).mp this
  have h3 : e (e.symm h) = h := e.apply_symm_apply h
  rw [he, h2] at h3
  simp only [OneMemClass.coe_one, mul_one] at h3
  rw [← h3]
  exact (e.symm h).1.2

/-- **Def. 5–6**: in a decomposition $G=G_1\times N$ as in Def. 5, every compact subgroup lies in $G_1$; so $G_1$ is
the maximal compact subgroup of $G$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Def. 5 (G₁ is the maximal compact subgroup)"]
theorem weil_VII_3_def5_maximal {G₁ N : Subgroup G} (e : (G₁ × N) ≃ₜ* G) (he : ∀ x, e x = (x.1 : G) * x.2)
    (hN : Nonempty (N ≃ₜ* Multiplicative ℝ) ∨ Nonempty (N ≃ₜ* Multiplicative ℤ))
    {H : Subgroup G} (hH : IsCompact (H : Set G)) : H ≤ G₁ := by
  rcases hN with ⟨f⟩ | ⟨f⟩
  · exact le_of_isCompact_aux e he (fun K hK x hx => eq_one_of_isCompact_real hK hx) f.some hH
  · exact le_of_isCompact_aux e he (fun K hK x hx => eq_one_of_isCompact_int hK hx) f.some hH

/-- **Def. 6** for a decomposition as in Def. 5: principal means trivial on $G_1$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Def. 6"]
theorem isPrincipal_iff_of_decomposition {G₁ N : Subgroup G} (hG₁ : IsCompact (G₁ : Set G))
    (e : (G₁ × N) ≃ₜ* G) (he : ∀ x, e x = (x.1 : G) * x.2)
    (hN : Nonempty (N ≃ₜ* Multiplicative ℝ) ∨ Nonempty (N ≃ₜ* Multiplicative ℤ)) (ω : Quasicharacter G) :
    IsPrincipalQuasicharacter ω ↔ ∀ g ∈ G₁, ω g = 1 := by
  constructor
  · intro h g hg
    exact h G₁ hG₁ g hg
  · intro h H hH x hx
    exact h x (weil_VII_3_def5_maximal e he hN hH hx)

end General

section IdeleClass

variable {F : Type} [Field F] [NumberField F]

variable (F) in
/-- The logarithm of the idele norm, as a morphism from the idele class group to $\mathbb R$ (written
multiplicatively). -/
def logNormHom : NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F →* Multiplicative ℝ where
  toFun c := Multiplicative.ofAdd (Real.log (Ideles.ideleClassNorm F c : ℝ))
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, NNReal.coe_mul]
    rw [Real.log_mul (Ideles.coe_ideleClassNorm_pos a).ne' (Ideles.coe_ideleClassNorm_pos b).ne']
    rfl

variable (F) in
theorem continuous_logNormHom : Continuous (logNormHom F) :=
  continuous_ofAdd.comp ((NNReal.continuous_coe.comp Ideles.continuous_ideleClassNorm).log
    fun c => (Ideles.coe_ideleClassNorm_pos c).ne')

/-- **Def. 6** for the idele class group of a number field: a Hecke character is principal if and only if it is
$|\cdot|^s$ for some $s\in\mathbb C$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Def. 6 (principal quasicharacters of the idele class group are |·|^s)"]
theorem weil_VII_3_def6_ideleClass (χ : HeckeCharacter F) :
    IsPrincipalQuasicharacter (G := NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F) χ ↔
      ∃ s : ℂ, χ = HeckeCharacter.normPow F s := by
  constructor
  · intro hp
    refine GlobalZeta.exists_eq_normPow_of_ideleOne fun b => ?_
    rw [HeckeCharacter.onIdeles_apply]
    refine hp (Ideles.IdeleClassGroup.normOne F) Ideles.IdeleClassGroup.isCompact_normOne _ ?_
    exact (Ideles.IdeleClassGroup.mem_normOne_mk _).mpr
      (Ideles.mem_ideleGroupOne_iff_mem_ideleOne.mpr (by simp))
  · rintro ⟨s, rfl⟩ H hH h hh
    have h1 := map_eq_one_of_isCompact (fun K hK x hx => eq_one_of_isCompact_real hK hx)
      (logNormHom F) (continuous_logNormHom F) hH hh
    have h2 : Real.log (Ideles.ideleClassNorm F h : ℝ) = 0 := by simpa [logNormHom] using h1
    have h3 : (Ideles.ideleClassNorm F h : ℝ) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (Ideles.coe_ideleClassNorm_pos h) h2
    apply Units.ext
    rw [HeckeCharacter.normPow_apply, h3, Complex.ofReal_one, Complex.one_cpow]
    rfl

end IdeleClass

end NumberFieldKB.WeilBNT
