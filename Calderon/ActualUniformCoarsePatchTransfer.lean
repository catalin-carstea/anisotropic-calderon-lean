import Calderon.ActualUniformCoarseKernelJets
import Calderon.MixedKernelConstruction.MixedKernelClosedCoarseSeed
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
attribute [local instance] Classical.propDecidable

theorem eqOn_product_full_lower_cross_on_retained
    (S : KnownSideSourceData) (L lambda : ℝ) (p : R3) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (F G : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lambda F (overlapRetained p r s))
    (hG : ProductSolutionOn S L lambda G (overlapRetained p r s))
    (hFcross : ∀ v ∈ overlapRetained p r s, lambda • v.1 ∈ S.W → F v = dilatedKernel2 S lambda v)
    (hGcross : ∀ v ∈ overlapRetained p r s, lambda • v.1 ∈ S.W → G v = dilatedKernel2 S lambda v)
    (hMeet : ∀ U : Set R3, IsOpen U → p ∈ U → ∃ x ∈ U, lambda • x ∈ S.W) :
    EqOn F G (overlapRetained p r s) := by
  let V : Set R3 := {y:R3 | 19*s/20<‖y-p‖ ∧ ‖y-p‖<21*s/20}
  let A : Set (R3×R3) := (ball p r ∩ (fun x:R3 => lambda • x) ⁻¹' S.W) ×ˢ V
  have hV : IsOpen V := isOpen_native_annulus _ _ _
  have hConn : IsConnected (overlapRetained p r s) :=
    (isConnected_ball hr).prod (isConnected_native_annulus p (19*s/20) (21*s/20) (by positivity) (by linarith))
  have hA : IsOpen A := (isOpen_ball.inter (S.W_open.preimage (continuous_const_smul lambda))).prod hV
  obtain ⟨x,hx,hxW⟩ := hMeet (ball p r) isOpen_ball (mem_ball_self hr)
  let y : R3 := p+s • EuclideanSpace.single (2:Fin 3) (1:ℝ)
  have hyN : ‖y-p‖ = s := by
    dsimp only [y]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    simp
  have hy : y ∈ V := by
    change 19*s/20<‖y-p‖ ∧ ‖y-p‖<21*s/20
    rw [hyN]
    constructor <;> linarith
  have hAne : A.Nonempty := ⟨(x,y),⟨hx,hxW⟩,hy⟩
  have hASub : A ⊆ overlapRetained p r s := fun _ hv => ⟨hv.1.1,hv.2⟩
  exact native_product_eq_on_connected_open S L lambda (isOpen_overlapRetained _ _ _) hConn
    hF hG hA hAne hASub (fun v hv => (hFcross v (hASub hv) hv.1.2).trans (hGcross v (hASub hv) hv.1.2).symm)

theorem uniform_coarse_patch_jets_of_full_lower_cross_solution (S : KnownSideSourceData) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1/4 ∧
      ∀ B s0 s1 : ℝ, 0 < B → 0 < s0 → s0 ≤ s1 →
      ∃ lambda0 : ℝ, ∃ C : ℕ → ℝ, 0 < lambda0 ∧ (∀ n, 0 < C n) ∧
      ∀ L lambda : ℝ, lambda ∈ Ioc (0:ℝ) lambda0 →
      ∀ p : R3, ‖p‖ ≤ B → S.separating_function (lambda • p) = 0 → ∀ s ∈ Icc s0 s1,
      ∀ r : ℝ, 0 < r → r ≤ α*s/1600 → ∀ (U : Set (R3×R3)) (H : R3×R3→ℝ),
      ProductSolutionOn S L lambda H U → overlapRetained p r s ⊆ U →
      (∀ v ∈ U, lambda • v.1 ∈ S.W → H v = dilatedKernel2 S lambda v) →
      ∀ n : ℕ, ∀ v ∈ overlapRetained p r s, ‖iteratedFDeriv ℝ n H v‖ ≤ C n := by
  obtain ⟨α,hα,hα4,HSeed⟩ := uniform_coarse_full_cross_kernel_with_uniform_jets S
  refine ⟨α,hα,hα4,?_⟩
  intro B s0 s1 hB hs0 hss
  obtain ⟨lK,C0,C,hlK,hC0,hC,HK⟩ := HSeed B s0 s1 hB hs0 hss
  obtain ⟨a,ha,HMeet⟩ := known_side_meets_open_at_separator S
  obtain ⟨lM,hlM,HM⟩ := exists_uniform_scaled_ball ha hB
  refine ⟨min lK lM,C,lt_min hlK hlM,hC,?_⟩
  intro L lambda hlambda p hp hp0 s hs r hr hrCap U H hH hCover hHcross n v hv
  have hlK' : lambda ∈ Ioc (0:ℝ) lK := ⟨hlambda.1,hlambda.2.trans (min_le_left _ _)⟩
  have hlM' : lambda ≤ lM := hlambda.2.trans (min_le_right _ _)
  obtain ⟨K,hRoom,hSol,hK1,hK2,hL2,hJets⟩ := HK L lambda hlK' p hp hp0 s hs
  have hspos : 0 < s := hs0.trans_le hs.1
  have hRetBig : overlapRetained p r s ⊆ overlapRetained p (α*s/1600) s :=
    Set.prod_mono (ball_subset_ball hrCap) subset_rfl
  have hRLarge : r ≤ α/4*(s/20) := by
    have hαs : 0 < α*s := mul_pos hα hspos
    linarith
  have hRetLarge : overlapRetained p r s ⊆ overlapLarge p (α/4*(s/20)) s :=
    overlapRetained_subset_large hRLarge
  have hMeet := HMeet lambda hlambda.1 p (HM lambda hlambda.1 hlM' p hp) hp0
  have hEq := eqOn_product_full_lower_cross_on_retained S L lambda p r s hr hspos H K
    (productSolutionOn_mono hH hCover) (productSolutionOn_mono hSol hRetLarge)
    (fun q hq hW => hHcross q (hCover hq) hW)
    (fun q hq hW => hK2 q (hRetLarge hq) hW) hMeet
  have hGerm : H =ᶠ[𝓝 v] K := Filter.eventually_of_mem ((isOpen_overlapRetained p r s).mem_nhds hv) fun q hq => hEq hq
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hJets n v (hRetBig hv)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
