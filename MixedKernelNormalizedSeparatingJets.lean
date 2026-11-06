import MixedKernelUniformLowerSide
import Calderon.CoordinateFieldWordDilation
import Calderon.LocalCoordinateWordLinearity
import Calderon.LocalCoordinateWordEqOnTransport
import Mathlib.Topology.Compactness.Compact
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology
open ActualReferenceDDHigherGeometryJets ActualReferenceLocalCoordinateWordJets

/-- Every nonempty ordered derivative of the normalized ORIGINAL phase has its exact dilation factor. -/
theorem normalized_separating_word_identity (psi : R3 → ℝ)
    (w : List (Fin 3)) (hw : w ≠ []) (lam : ℝ) (hlam : lam ≠ 0) (x : R3) :
    coordinateFieldWordPartial w (fun y => -lam⁻¹ * psi (lam • y)) x =
      -(lam^(w.length-1)*coordinateFieldWordPartial w psi (lam • x)) := by
  change coordinateFieldWordPartial w (fun y => (-lam⁻¹) • psi (lam • y)) x = _
  rw [coordinateFieldWordPartial_const_smul]
  change (-lam⁻¹) • coordinateFieldWordPartial w (fun y => psi (lam • y)) x = _
  rw [coordinateFieldWordPartial_comp_const_smul]
  simp only [smul_eq_mul]
  have hn : 0 < w.length := List.length_pos_iff_ne_nil.mpr hw
  have hpow : lam^w.length = lam^(w.length-1)*lam := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp [hlam]
  <;> ring

/-- A compact physical set turns pointwise parameter continuity at zero into one uniform ceiling. -/
theorem exists_uniform_parameter_error_on_compact
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    (K : Set X) (hK : IsCompact K) (F : ℝ × X → V) (c : V)
    (hF : ∀ x ∈ K, ContinuousAt F (0,x)) (hzero : ∀ x ∈ K, F (0,x) = c)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam ∈ Icc (0 : ℝ) lam0,
      ∀ x ∈ K, ‖F (lam,x)-c‖ < eps := by
  let P : Set (ℝ × X) := {z | ‖F z-c‖ < eps}
  have hKP : ({0} : Set ℝ) ×ˢ K ⊆ interior P := by
    rintro z ⟨hz,hx⟩
    have hz0 : z.1 = 0 := mem_singleton_iff.mp hz
    have hcont : ContinuousAt (fun z : ℝ × X => ‖F z-c‖) (0,z.2) :=
      ((hF z.2 hx).sub continuousAt_const).norm
    have hp : P ∈ 𝓝 (0,z.2) := hcont.preimage_mem_nhds
      (isOpen_Iio.mem_nhds (by simpa only [mem_Iio,hzero z.2 hx,sub_self,norm_zero] using heps))
    have hi := mem_interior_iff_mem_nhds.mpr hp
    change (z.1,z.2) ∈ interior P
    rw [hz0]
    exact hi
  obtain ⟨I,V,hI,hV,h0I,hKV,hIV⟩ :=
    generalized_tube_lemma isCompact_singleton hK isOpen_interior hKP
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hI 0 (h0I (mem_singleton 0))
  refine ⟨r/2,half_pos hr,fun lam hlam x hx => ?_⟩
  have hlI : lam ∈ I := hball (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hlam.1]
    linarith [hlam.2])
  have hpair : (lam,x) ∈ P := (interior_subset : interior P ⊆ P) (hIV ⟨hlI,hKV hx⟩)
  exact hpair

/-- The nonsingular jet field is continuous at every zero-dilation point on the actual source data. -/
theorem continuousAt_original_normalized_separating_jet (S : KnownSideSourceData)
    (w : List (Fin 3)) (x : R3) :
    ContinuousAt (fun z : ℝ × R3 =>
      -(z.1^(w.length-1)*coordinateFieldWordPartial w S.separating_function (z.1 • z.2))) (0,x) := by
  have hword : ContinuousAt (coordinateFieldWordPartial w S.separating_function) (0 : R3) :=
    ((contDiffOn_coordinateFieldWordPartial w S.separating_function S.coordinateRoom
      S.coordinateRoom_open S.separating_function_smooth).contDiffAt
        (S.coordinateRoom_open.mem_nhds S.origin_mem)).continuousAt
  have hscale : ContinuousAt (fun z : ℝ × R3 => z.1 • z.2) (0,x) :=
    continuousAt_fst.smul continuousAt_snd
  have hwcomp : ContinuousAt
      (fun z : ℝ × R3 => coordinateFieldWordPartial w S.separating_function (z.1 • z.2)) (0,x) := by
    have hword' : ContinuousAt (coordinateFieldWordPartial w S.separating_function)
        ((0 : ℝ) • x) := by simpa only [zero_smul] using hword
    exact hword'.comp (f := fun z : ℝ × R3 => z.1 • z.2) (x := (0,x)) hscale
  exact ((continuousAt_fst.pow _).mul hwcomp).neg

/-- Any finite family of the actual nonempty coordinate words converges uniformly on a bounded set. -/
theorem exists_uniform_original_normalized_separating_words (S : KnownSideSourceData)
    (W : Finset (List (Fin 3))) (hW : ∀ w ∈ W, w ≠ [])
    (B eps : ℝ) (hB : 0 < B) (heps : 0 < eps) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ x : R3, ‖x‖ ≤ B → ∀ w ∈ W,
        |coordinateFieldWordPartial w (fun y => -lam⁻¹*S.separating_function (lam • y)) x -
          (if w.length = 1 then -coordinateFieldWordPartial w S.separating_function 0 else 0)| < eps := by
  classical
  have H : ∀ w : List (Fin 3), w ≠ [] → ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ x : R3, ‖x‖ ≤ B →
        |coordinateFieldWordPartial w (fun y => -lam⁻¹*S.separating_function (lam • y)) x -
          (if w.length = 1 then -coordinateFieldWordPartial w S.separating_function 0 else 0)| < eps := by
    intro w hw
    let F : ℝ × R3 → ℝ := fun z =>
      -(z.1^(w.length-1)*coordinateFieldWordPartial w S.separating_function (z.1 • z.2))
    let c := if w.length = 1 then -coordinateFieldWordPartial w S.separating_function 0 else 0
    have hzero : ∀ x ∈ closedBall (0 : R3) B, F (0,x) = c := by
      intro x hx
      have hn : 0 < w.length := List.length_pos_iff_ne_nil.mpr hw
      by_cases h1 : w.length = 1
      · simp [F,c,h1]
      · have hpos : 0 < w.length-1 := by omega
        simp [F,c,h1,zero_pow (Nat.ne_of_gt hpos)]
    obtain ⟨lam0,hpos,H0⟩ := exists_uniform_parameter_error_on_compact
      (closedBall (0 : R3) B) (isCompact_closedBall _ _) F c
      (fun x hx => continuousAt_original_normalized_separating_jet S w x) hzero eps heps
    refine ⟨lam0,hpos,fun lam hlam hsmall x hx => ?_⟩
    have hxK : x ∈ closedBall (0 : R3) B := by simpa only [mem_closedBall,dist_zero_right] using hx
    rw [normalized_separating_word_identity _ w hw lam hlam.ne' x]
    simpa only [Real.norm_eq_abs,F,c] using H0 lam ⟨hlam.le,hsmall⟩ x hxK
  revert hW
  induction W using Finset.induction_on with
  | empty =>
    intro hW
    exact ⟨1,one_pos,fun lam hlam hsmall x hx w hw => False.elim (Finset.notMem_empty _ hw)⟩
  | @insert w W hw ih =>
    intro hW
    obtain ⟨lw,hlw,Hw⟩ := H w (hW w (Finset.mem_insert_self _ _))
    obtain ⟨lW,hlW,HW⟩ := ih (fun v hv => hW v (Finset.mem_insert_of_mem hv))
    refine ⟨min lw lW,lt_min hlw hlW,fun lam hlam hsmall x hx v hv => ?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Hw lam hlam (hsmall.trans (min_le_left _ _)) x hx
    · exact HW lam hlam (hsmall.trans (min_le_right _ _)) x hx v hv

/-- The normalized ORIGINAL defining function converges with every prescribed finite ordered jet. -/
theorem exists_uniform_original_normalized_separating_finite_jets
    (S : KnownSideSourceData) (N : ℕ) (B eps : ℝ) (hB : 0 < B) (heps : 0 < eps) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ x : R3, ‖x‖ ≤ B → lam • x ∈ S.coordinateRoom ∧
        |-lam⁻¹*S.separating_function (lam • x)+x 2| ≤ eps ∧
        ∀ w : List (Fin 3), w ≠ [] → w.length ≤ N →
          |coordinateFieldWordPartial w (fun y => -lam⁻¹*S.separating_function (lam • y)) x -
            (if w.length = 1 then -coordinateFieldWordPartial w S.separating_function 0 else 0)| < eps := by
  classical
  let W0 : Finset (List (Fin 3)) := Finset.univ.image
    (fun i : BoundedCoordinateWord N => List.ofFn i.2)
  let W := W0.filter (fun w => w ≠ [])
  have hW : ∀ w ∈ W, w ≠ [] := fun w hw => (Finset.mem_filter.mp hw).2
  have hmem : ∀ w : List (Fin 3), w ≠ [] → w.length ≤ N → w ∈ W := by
    intro w hw hn
    apply Finset.mem_filter.mpr
    refine ⟨?_,hw⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨⟨w.length,Nat.lt_succ_iff.mpr hn⟩,w.get⟩,Finset.mem_univ _,List.ofFn_get w⟩
  obtain ⟨lJ,hlJ,HJ⟩ := exists_uniform_original_normalized_separating_words S W hW B eps hB heps
  obtain ⟨lV,hlV,HV⟩ := exists_uniform_scaled_separating_error S B (2*eps) hB (by positivity)
  refine ⟨min lJ lV,lt_min hlJ hlV,fun lam hlam hsmall x hx => ?_⟩
  have hv := HV lam hlam (hsmall.trans (min_le_right _ _)) x hx
  refine ⟨hv.1,?_,fun w hw hn => HJ lam hlam (hsmall.trans (min_le_left _ _)) x hx w (hmem w hw hn)⟩
  have hid : -lam⁻¹*S.separating_function (lam • x)+x 2 =
      (-lam⁻¹)*(S.separating_function (lam • x)-lam*x 2) := by
    field_simp [hlam.ne']
    <;> ring
  rw [hid,abs_mul,abs_neg,abs_inv,abs_of_pos hlam]
  calc lam⁻¹*|S.separating_function (lam • x)-lam*x 2|
      ≤ lam⁻¹*(lam*(2*eps)/2) := mul_le_mul_of_nonneg_left hv.2.1 (inv_pos.mpr hlam).le
    _ = eps := by field_simp [hlam.ne'] <;> ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
