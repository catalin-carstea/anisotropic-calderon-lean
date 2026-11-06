import Calderon.ActualMainOriginalSourceTransfer
import Calderon.FixedExteriorSourceBall

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  ReferenceWeightedApproximation ConformalDepth

theorem exists_known_side_source_data_with_source_free_room
    (S : KnownSideSourceData) (hFirst : ‖S.Xi1 0‖ ≤ 1) (hSecond : ‖S.Xi2 0‖ ≤ 1) :
    ∃ T : KnownSideSourceData,
      T.hreg = S.hreg ∧ T.hcalc = S.hcalc ∧
      T.original1 = S.original1 ∧ T.original2 = S.original2 ∧
      T.K1 = S.K1 ∧ T.K2 = S.K2 ∧ T.G1 = S.G1 ∧ T.G2 = S.G2 ∧
      T.Xi1 = S.Xi1 ∧ T.Xi2 = S.Xi2 ∧ T.g1 = S.g1 ∧ T.g2 = S.g2 ∧
      T.separating_function = S.separating_function ∧
      T.coordinateRoom ⊆ S.coordinateRoom ∧ T.W = S.W ∩ T.coordinateRoom ∧
      (∀ x ∈ T.coordinateRoom,
        T.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
        T.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3)) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        (∀ x ∈ S.W,
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
          radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) →
        ∀ x ∈ T.W,
          radiusTwoSmoothSourceResponse T.hreg T.hcalc T.original1 T.original1_admissible s (T.Xi1 x) =
          radiusTwoSmoothSourceResponse T.hreg T.hcalc T.original2 T.original2_admissible s (T.Xi2 x) := by
  classical
  have hOutside (x : R3) (hx : ‖x‖ < (5/4 : ℝ)) :
      x ∉ closure (fixedExteriorSourceOpens : Set R3) := by
    intro hIn
    have hClosed : closure (fixedExteriorSourceOpens : Set R3) ⊆
        closedBall fixedExteriorSourceCenter (1/8 : ℝ) := by
      change closure (ball fixedExteriorSourceCenter (1/8 : ℝ)) ⊆ _
      exact closure_minimal ball_subset_closedBall isClosed_closedBall
    have hd : ‖fixedExteriorSourceCenter - x‖ ≤ (1/8 : ℝ) := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hClosed hIn
    have hn := norm_le_norm_sub_add fixedExteriorSourceCenter x
    rw [norm_fixedExteriorSourceCenter] at hn
    linarith
  let U1 : Set R3 := S.coordinateRoom ∩ S.Xi1 ⁻¹' ball (0 : R3) (5/4 : ℝ)
  let U2 : Set R3 := S.coordinateRoom ∩ S.Xi2 ⁻¹' ball (0 : R3) (5/4 : ℝ)
  let U := U1 ∩ U2
  have hU1 : IsOpen U1 :=
    S.Xi1_smooth.continuousOn.isOpen_inter_preimage S.coordinateRoom_open isOpen_ball
  have hU2 : IsOpen U2 :=
    S.Xi2_smooth.continuousOn.isOpen_inter_preimage S.coordinateRoom_open isOpen_ball
  have hU : IsOpen U := hU1.inter hU2
  have hSub : U ⊆ S.coordinateRoom := fun x hx => hx.1.1
  have h0 : (0 : R3) ∈ U := by
    refine ⟨⟨S.origin_mem,?_⟩,⟨S.origin_mem,?_⟩⟩
    · exact mem_ball_zero_iff.mpr (by linarith)
    · exact mem_ball_zero_iff.mpr (by linarith)
  obtain ⟨e,he,hBallU⟩ := Metric.isOpen_iff.mp hU 0 h0
  obtain ⟨a,ha,hBallA,hSide⟩ := S.one_sided_room
  let b := min a e
  have hb : 0 < b := lt_min ha he
  have hBA : ball (0 : R3) b ⊆ ball (0 : R3) a := ball_subset_ball (min_le_left a e)
  have hBU : ball (0 : R3) b ⊆ U :=
    (ball_subset_ball (min_le_right a e)).trans hBallU
  have hNewSide : ∃ b : ℝ, 0 < b ∧ ball (0 : R3) b ⊆ U ∧
      {z ∈ ball (0 : R3) b | S.separating_function z < 0} ⊆ S.W ∩ U := by
    refine ⟨b,hb,hBU,?_⟩
    intro z hz
    exact ⟨hSide ⟨hBA hz.1,hz.2⟩,hBU hz.1⟩
  let T : KnownSideSourceData := {
    S with
    coordinateRoom := U
    coordinateRoom_open := hU
    origin_mem := h0
    Xi1_smooth := S.Xi1_smooth.mono hSub
    Xi2_smooth := S.Xi2_smooth.mono hSub
    Xi1_injective := by
      intro x hx y hy hxy
      exact S.Xi1_injective (hSub hx) (hSub hy) hxy
    Xi2_injective := by
      intro x hx y hy hxy
      exact S.Xi2_injective (hSub hx) (hSub hy) hxy
    Xi1_jacobian := fun x hx => S.Xi1_jacobian x (hSub hx)
    Xi2_jacobian := fun x hx => S.Xi2_jacobian x (hSub hx)
    Xi1_room := fun x hx => S.Xi1_room x (hSub hx)
    Xi2_room := fun x hx => S.Xi2_room x (hSub hx)
    carrier1 := by
      intro x hx
      exact S.carrier1 (hSub hx)
    carrier2 := by
      intro x hx
      exact S.carrier2 (hSub hx)
    harmonic_coordinates1 := fun i x hx => S.harmonic_coordinates1 i x (hSub hx)
    harmonic_coordinates2 := fun i x hx => S.harmonic_coordinates2 i x (hSub hx)
    W := S.W ∩ U
    W_open := S.W_open.inter hU
    W_room := fun x hx => hx.2
    metrics_match := by
      intro x hx
      exact S.metrics_match hx.1
    kernels_match := by
      intro x hx y hy hxy
      exact S.kernels_match x hx.1 y hy.1 hxy
    separating_function_smooth := S.separating_function_smooth.mono hSub
    one_sided_room := hNewSide }
  refine ⟨T,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hSub,rfl,?_,?_⟩
  · intro x hx
    change S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3)
    have hxU : x ∈ U := hx
    exact ⟨hOutside _ (mem_ball_zero_iff.mp hxU.1.2),
      hOutside _ (mem_ball_zero_iff.mp hxU.2.2)⟩
  · intro s hMatch x hx
    exact hMatch x hx.1

theorem source_support_avoidance_on_actual_transfer_family
    (S : KnownSideSourceData)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (L lam delta Rstar bound separation : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (s : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    (∀ y ∈ cylinder, S.Xi1 (lam • y) ∉ tsupport s) ∧
    (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ z ∈ closedBall (0 : R3) 1, S.Xi1 (lam • packetEndpoint S L (cover.packet i)
        lam y (referenceRadius delta Rstar p L y) z) ∉ tsupport s) ∧
    (∀ y ∈ cylinder, S.Xi2 (lam • y) ∉ tsupport s) := by
  have hCenter : ∀ y ∈ cylinder, lam • y ∈ S.coordinateRoom := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y hy
    have he : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : R3) ∈ sphere (0 : R3) 1 := by
      simp
    obtain ⟨_,hyRoom,_⟩ := K.domain_room (K.sphere_cover i y ⟨hy,hi⟩ _ he)
    exact hyRoom
  have hAvoid1 (x : R3) (hx : x ∈ S.coordinateRoom) : S.Xi1 x ∉ tsupport s := by
    intro hs
    exact (hFree x hx).1 (subset_closure (s.tsupport_subset hs))
  have hAvoid2 (x : R3) (hx : x ∈ S.coordinateRoom) : S.Xi2 x ∉ tsupport s := by
    intro hs
    exact (hFree x hx).2 (subset_closure (s.tsupport_subset hs))
  refine ⟨fun y hy => hAvoid1 _ (hCenter y hy),?_,fun y hy => hAvoid2 _ (hCenter y hy)⟩
  intro i y hy z hz
  apply hAvoid1
  exact cover.coordinate_room i lam hLam y hy.2 (referenceRadius delta Rstar p L y)
    (referenceRadius_pos delta Rstar p L y hdelta hRstar) (hRadius y hy.1) z
    (closedBall_subset_closedBall (by norm_num) hz)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
