import NumberFieldKB.WeilBNT.FunctionField.FourierFF

/-!
# Self-duality of the adeles of a function field: the topological part (Weil IV.§2 Thm. 3, $E=k$)

$k$ is a global function field with field of constants $\mathbb F_q$, $\psi_0\ne1$ a character of $\mathbb F_q$ and
$\chi=\psi_0\circ\hat\omega$ the basic character of $k_{\mathbb A}$ (`FFAdeleRing.chiA`, `FunctionField/SelfDuality.lean`).

* **`FFAdeleRing.weil_IV_2_thm3_ff_isEmbedding`**: $a\mapsto(x\mapsto\chi(ax))$ is a topological embedding of
  $k_{\mathbb A}$ into $C(k_{\mathbb A},\mathbb T)$ with the compact-open topology.
* **`FFAdeleRing.range_chiAMul`**: its image is exactly the set of continuous characters.

Together with `weil_IV_2_thm3_ff_char` this is the first assertion of Weil IV.§2 Thm. 3 for $E=k$: the map is an
isomorphism of $k_{\mathbb A}$ onto its dual, a homeomorphism onto the group of characters with the compact-open
topology. Proof of the embedding (as for number fields, `weil_IV_2_thm3_isEmbedding`): a neighbourhood of $0$
contains some $U(\mathfrak b)$; if $\chi(a\,\cdot)$ maps the compact set $U(\mathfrak c-\mathfrak b)$ into the right
half-plane, then it maps it to $1$ (the image is a subgroup, and the circle has no small subgroups), so
$a\in U(\mathfrak b)$ (`exists_chiA_ne_one`).
-/

open Topology Filter

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

namespace FFAdeleRing

variable (ψ₀ : AddChar Fq Circle)

/-- The character $x\mapsto\chi(ax)$ of $k_{\mathbb A}$, as a continuous map. -/
def chiAMul (a : FFAdeleRing Fq k) : C(FFAdeleRing Fq k, Circle) :=
  ⟨fun x => chiA ψ₀ (a * x), (continuous_chiA ψ₀).comp (continuous_const.mul continuous_id)⟩

theorem chiAMul_apply (a x : FFAdeleRing Fq k) : chiAMul ψ₀ a x = chiA ψ₀ (a * x) := rfl

/-- $x\mapsto\chi(ax)$ as an additive character. -/
def chiAMulChar (a : FFAdeleRing Fq k) : AddChar (FFAdeleRing Fq k) Circle :=
  (chiA ψ₀).compAddMonoidHom (AddMonoidHom.mulLeft a)

theorem chiAMul_injective (hψ₀ : ψ₀ ≠ 1) : Function.Injective (chiAMul (Fq := Fq) (k := k) ψ₀) := by
  intro a b hab
  obtain ⟨c, -, hc⟩ := weil_IV_2_thm3_ff_char ψ₀ hψ₀ (chiAMulChar ψ₀ a)
    (chiAMul ψ₀ a).continuous
  have ha := hc a fun x => rfl
  have hb := hc b fun x => by
    show chiA ψ₀ (a * x) = chiA ψ₀ (b * x)
    exact DFunLike.congr_fun hab x
  exact ha.trans hb.symm

/-- **The image of $a\mapsto\chi(a\,\cdot)$ is the set of continuous characters of $k_{\mathbb A}$.** -/
theorem range_chiAMul (hψ₀ : ψ₀ ≠ 1) :
    Set.range (chiAMul (Fq := Fq) (k := k) ψ₀) =
      {f | f 0 = 1 ∧ ∀ x y, f (x + y) = f x * f y} := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨by rw [chiAMul_apply, mul_zero]; exact AddChar.map_zero_eq_one _, fun x y => ?_⟩
    rw [chiAMul_apply, chiAMul_apply, chiAMul_apply, mul_add]
    exact AddChar.map_add_eq_mul _ _ _
  · rintro ⟨h0, hadd⟩
    let ψ : AddChar (FFAdeleRing Fq k) Circle :=
      { toFun := f, map_zero_eq_one' := h0, map_add_eq_mul' := hadd }
    obtain ⟨a, ha, -⟩ := weil_IV_2_thm3_ff_char ψ₀ hψ₀ ψ f.continuous
    exact ⟨a, ContinuousMap.ext fun x => (ha x).symm⟩

/-- If $\chi(a\,\cdot)$ maps $U(\mathfrak b)$ into the right half-plane, it is trivial on $U(\mathfrak b)$. -/
theorem chiA_mul_eq_one_of_mapsTo {b : Divisor Fq k} {a : FFAdeleRing Fq k} {W : Set Circle}
    (hW : ∀ H : Subgroup Circle, (H : Set Circle) ⊆ W → H = ⊥)
    (h : Set.MapsTo (fun x => chiA ψ₀ (a * x)) (U b) W) {x : FFAdeleRing Fq k} (hx : x ∈ U b) :
    chiA ψ₀ (a * x) = 1 := by
  have hH := hW (Subgroup.zpowers (chiA ψ₀ (a * x))) (by
    rintro _ ⟨m, rfl⟩
    have hmx : m • x ∈ U b := (U b).zsmul_mem hx m
    have := h hmx
    simp only at this
    show chiA ψ₀ (a * x) ^ m ∈ W
    rw [mul_smul_comm, AddChar.map_zsmul_eq_zpow] at this
    exact this)
  have : chiA ψ₀ (a * x) ∈ Subgroup.zpowers (chiA ψ₀ (a * x)) := Subgroup.mem_zpowers _
  rw [hH] at this
  exact this

/-- **Weil, IV.§2, Thm. 3, first assertion, $E=k$ a function field, topological part**: $a\mapsto\chi(a\,\cdot)$ is
a homeomorphism of $k_{\mathbb A}$ onto its image in $C(k_{\mathbb A},\mathbb T)$ (compact-open topology), which is
the group of continuous characters (`range_chiAMul`). -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3 (p. 66), first assertion, E = k, function fields: the map is a homeomorphism onto the dual"]
theorem weil_IV_2_thm3_ff_isEmbedding (hψ₀ : ψ₀ ≠ 1) : IsEmbedding (chiAMul (Fq := Fq) (k := k) ψ₀) := by
  have hcont : Continuous (chiAMul (Fq := Fq) (k := k) ψ₀) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      ((continuous_chiA ψ₀).comp (continuous_fst.mul continuous_snd))
  let g : FFAdeleRing Fq k →+ Additive C(FFAdeleRing Fq k, Circle) :=
    { toFun := fun a => Additive.ofMul (chiAMul ψ₀ a)
      map_zero' := by
        refine congrArg Additive.ofMul (ContinuousMap.ext fun x => ?_)
        show chiA ψ₀ (0 * x) = 1
        rw [zero_mul]; exact AddChar.map_zero_eq_one _
      map_add' := fun a b => by
        refine congrArg Additive.ofMul (ContinuousMap.ext fun x => ?_)
        show chiA ψ₀ ((a + b) * x) = chiA ψ₀ (a * x) * chiA ψ₀ (b * x)
        rw [add_mul]; exact AddChar.map_add_eq_mul _ _ _ }
  obtain ⟨W0, hW0, hW0H⟩ := ff_circle_noSmallSubgroups
  obtain ⟨W, hWsub, hWopen, hW1⟩ := mem_nhds_iff.1 hW0
  have hg : IsInducing g := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ ?_
    swap
    · intro V hV
      obtain ⟨b, hb⟩ := exists_U_subset_of_mem_nhds_zero hV
      set C : Set (FFAdeleRing Fq k) := (U (canonical Fq k - b) : Set (FFAdeleRing Fq k))
      have hC : IsCompact C := isCompact_U _
      have hO : IsOpen {f : C(FFAdeleRing Fq k, Circle) | Set.MapsTo f C W} :=
        ContinuousMap.isOpen_setOfPred_mapsTo hC hWopen
      refine Filter.mem_comap.mpr ⟨{h : Additive C(FFAdeleRing Fq k, Circle) | Set.MapsTo h.toMul C W},
        hO.mem_nhds ?_, ?_⟩
      · intro x _
        show ((1 : C(FFAdeleRing Fq k, Circle)) x : Circle) ∈ W
        exact hW1
      · intro a ha
        apply hb
        by_contra hab
        have hab' : a ∉ U (canonical Fq k - (canonical Fq k - b)) := by
          rwa [sub_sub_cancel]
        obtain ⟨u, hu, hne⟩ := exists_chiA_ne_one ψ₀ hψ₀ hab'
        apply hne
        rw [mul_comm]
        exact chiA_mul_eq_one_of_mapsTo ψ₀ (fun H hH => hW0H H (hH.trans hWsub))
          (fun x hx => ha hx) hu
    · intro V hV
      obtain ⟨T, hT, hTV⟩ := Filter.mem_comap.mp hV
      have hc : Filter.Tendsto g (𝓝 0) (𝓝 0) := by
        have : ContinuousAt g 0 := (show Continuous g from hcont).continuousAt
        rwa [ContinuousAt, map_zero] at this
      exact Filter.mem_of_superset (hc hT) hTV
  exact ⟨hg, chiAMul_injective ψ₀ hψ₀⟩

end FFAdeleRing

end

end NumberFieldKB.WeilBNT.FF
