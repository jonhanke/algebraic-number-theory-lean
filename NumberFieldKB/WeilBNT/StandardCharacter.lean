import NumberFieldKB.WeilBNT.AdeleAnnihilator
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocal
import QuadFormsKB.Analysis.DifferentLocal

/-!
# Weil, *Basic Number Theory*, Chapter IV, §2, Corollary 1 of Theorem 3, for the standard character

$k$ is a number field and $\chi$ = `chiA` the standard character of $k_{\mathbb A}$ (`AdeleAnnihilator.lean`),
non-trivial and trivial on $k$. For a place $v$, $\chi_v$ is the character induced by $\chi$ on the quasifactor $k_v$
($x\mapsto\chi$ of the adele with $x$ at $v$ and $0$ elsewhere: `chiAtFinite`, `chiAtInfinite`).

**Cor. 1** (p. 69): for every $v$, $\chi_v$ is non-trivial, and for almost all finite places $v$, $\chi_v$ has order $0$
in the sense of II.§5 Def. 4, i.e. the set of $y\in k_v$ with $\chi_v(xy)=1$ for all $x\in r_v$ is exactly $r_v$.

* **`chiAtFinite_eq`**: $\chi_v=\psi_v$ (QuadFormsKB's local character $\psi_p\circ\operatorname{Tr}_{k_v/\mathbb Q_p}$);
* **`weil_IV_2_thm3_cor1_finite`**, **`weil_IV_2_thm3_cor1_infinite`**: $\chi_v$ is non-trivial at every place;
* **`weil_IV_2_thm3_cor1_order`**: $\chi_v$ has order $0$ for all but finitely many finite places $v$.

Weil derives Cor. 1 for every character as in Thm. 3 from the self-duality of $k_{\mathbb A}$; for the standard character
it is a direct computation: the annihilator of $r_v$ under $\psi_v$ is the local inverse different
$\mathfrak p_v^{-d_v}$ (QuadFormsKB `annihV_latticeV`), and $d_v=0$ for almost all $v$
(QuadFormsKB `finite_support_diffExp`).
-/

open IsDedekindDomain NumberField QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable (K : Type) [Field K] [NumberField K]

/-- The character $\chi_v$ induced by the standard character on the quasifactor $k_v$, $v$ finite. -/
def chiAtFinite (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : Circle :=
  chiA K ((0, singleAdele v x) : AdeleRing (𝓞 K) K)

open Classical in
/-- The character $\chi_w$ induced by the standard character on the quasifactor $k_w$, $w$ infinite. -/
def chiAtInfinite (w : InfinitePlace K) (x : w.Completion) : Circle :=
  chiA K ((Pi.single w x, 0) : AdeleRing (𝓞 K) K)

variable {K}

/-- At a finite place, $\chi_v$ is QuadFormsKB's local character $\psi_v$. -/
theorem chiAtFinite_eq (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : chiAtFinite K v x = psiV v x := by
  classical
  unfold chiAtFinite chiA
  change chiInf K 0 * chiFin K (singleAdele v x) = psiV v x
  rw [chiInf_zero, one_mul]
  unfold chiFin
  rw [finprod_eq_single _ v]
  · exact congrArg (psiV v) (singleAdele_apply_self v x)
  · intro u hu
    have : (singleAdele v x) u = 0 := singleAdele_apply_ne hu x
    change psiV u ((singleAdele v x) u) = 1
    rw [this]
    exact AddChar.map_zero_eq_one _

/-- **Weil, IV.§2, Cor. 1 of Thm. 3**, finite places: $\chi_v$ is non-trivial. -/
@[kb "weil1973bnt" "Ch. IV, §2, Cor. 1 of Thm. 3 (p. 69), non-triviality at finite places, standard character, number field case"]
theorem weil_IV_2_thm3_cor1_finite (v : HeightOneSpectrum (𝓞 K)) : ∃ x, chiAtFinite K v x ≠ 1 :=
  ⟨_, by rw [chiAtFinite_eq]; exact psiV_nontrivial v⟩

open Classical in
theorem traceInf_single_real (w : InfinitePlace K) (hw : w.IsReal) (x : w.Completion) :
    traceInf (InfiniteAdeleRing.ringEquiv_mixedSpace K (Pi.single w x)) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x := by
  unfold traceInf
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  dsimp only
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {u : InfinitePlace K // u.IsComplex})) ?_, add_zero,
    Finset.sum_eq_single (⟨w, hw⟩ : {u : InfinitePlace K // u.IsReal})]
  · simp
  · intro u _ hne
    have hu : u.1 ≠ w := fun h => hne (Subtype.ext h)
    rw [Pi.single_eq_of_ne hu, map_zero]
  · simp
  · intro u _
    have hu : u.1 ≠ w := fun h => (InfinitePlace.not_isReal_iff_isComplex.mpr u.2) (h ▸ hw)
    rw [Pi.single_eq_of_ne hu, map_zero]
    simp

open Classical in
theorem traceInf_single_complex (w : InfinitePlace K) (hw : w.IsComplex) (x : w.Completion) :
    traceInf (InfiniteAdeleRing.ringEquiv_mixedSpace K (Pi.single w x)) =
      2 * (InfinitePlace.Completion.extensionEmbedding w x).re := by
  unfold traceInf
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  dsimp only
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {u : InfinitePlace K // u.IsReal})) ?_, zero_add,
    Finset.sum_eq_single (⟨w, hw⟩ : {u : InfinitePlace K // u.IsComplex})]
  · simp
  · intro u _ hne
    have hu : u.1 ≠ w := fun h => hne (Subtype.ext h)
    rw [Pi.single_eq_of_ne hu, map_zero]
    simp
  · simp
  · intro u _
    have hu : u.1 ≠ w := fun h => (InfinitePlace.not_isReal_iff_isComplex.mpr hw) (h ▸ u.2)
    rw [Pi.single_eq_of_ne hu, map_zero]

/-- **Weil, IV.§2, Cor. 1 of Thm. 3**, infinite places: $\chi_w$ is non-trivial. -/
@[kb "weil1973bnt" "Ch. IV, §2, Cor. 1 of Thm. 3 (p. 69), non-triviality at infinite places, standard character, number field case"]
theorem weil_IV_2_thm3_cor1_infinite (w : InfinitePlace K) : ∃ x, chiAtInfinite K w x ≠ 1 := by
  classical
  have key : ∀ x : w.Completion, chiAtInfinite K w x =
      psiInf (InfiniteAdeleRing.ringEquiv_mixedSpace K (Pi.single w x)) := by
    intro x
    unfold chiAtInfinite chiA
    change chiInf K (Pi.single w x) * chiFin K 0 = _
    rw [chiFin_zero, mul_one]
    rfl
  by_cases hw : w.IsReal
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (1 / 2), ?_⟩
    rw [key]
    intro h
    obtain ⟨n, hn⟩ := (fourierChar_eq_one_iff _).mp h
    rw [traceInf_single_real w hw, ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      RingEquiv.apply_symm_apply] at hn
    have h2 : (2 : ℝ) * n = 1 := by linarith
    have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h2
    omega
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (1 / 4 : ℝ), ?_⟩
    rw [key]
    intro h
    obtain ⟨n, hn⟩ := (fourierChar_eq_one_iff _).mp h
    rw [traceInf_single_complex w hc, ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hc,
      RingEquiv.apply_symm_apply] at hn
    simp only [Complex.ofReal_re] at hn
    have h2 : (2 : ℝ) * n = 1 := by linarith
    have h3 : (2 : ℤ) * n = 1 := by exact_mod_cast h2
    omega

/-- **Weil, IV.§2, Cor. 1 of Thm. 3**, order: for all but finitely many finite places $v$, $\chi_v$ has order $0$: the
$y\in k_v$ with $\chi_v(xy)=1$ for every $x\in r_v$ are exactly the elements of $r_v$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Cor. 1 of Thm. 3 (p. 69), order 0 at almost all places, standard character, number field case"]
theorem weil_IV_2_thm3_cor1_order :
    {v : HeightOneSpectrum (𝓞 K) |
      {y : v.adicCompletion K | ∀ x : v.adicCompletion K, Valued.v x ≤ 1 → chiAtFinite K v (x * y) = 1} ≠
        {y | Valued.v y ≤ 1}}.Finite := by
  refine (finite_support_diffExp (F := K)).subset fun v hv => ?_
  by_contra hd
  apply hv
  have hd' : (diffExp v : ℤ) = 0 := by simpa using hd
  have h := annihV_latticeV v 0
  rw [hd'] at h
  ext y
  have hy := Set.ext_iff.mp h y
  simp only [annihV, SetLike.mem_coe, mem_latticeV, Set.mem_ofPred_eq] at hy ⊢
  simp only [chiAtFinite_eq]
  simpa using hy

end NumberFieldKB.WeilBNT
