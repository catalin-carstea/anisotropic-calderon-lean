import Calderon.ActualMixedKernelScalarTransfer
import Calderon.ReferenceFramedNormalizedEndpointIntegralIdentities
import Calderon.ActualMixedKernelGlobalSurfaceExtension

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalCoordinatesFrame ReferenceWeightedApproximation DirichletFamily.DriftBootstrap

theorem exists_packetEndpoint_signed_radius_bound_on_compact
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (K : Set R3) (hCompact : IsCompact K) (R : ℝ) (hR0 : 0 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ K ∩ P.centers,
      ∀ r ∈ Icc (-R) R, ∀ z ∈ closedBall (0 : R3) 1,
        ‖packetEndpoint S L P lam y r z - y‖ ≤ C * |r| := by
  classical
  have hData : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B :=
    P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞
      (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := by
    rcases hData with ⟨_, _, _, _, _, _, _, hTheta, _, _, _⟩
    exact hTheta
  let Q : ReferenceEndpointVariables → R3 :=
    referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi
  have hQ : ContDiff ℝ ∞ Q :=
    contDiff_referenceFramedNormalizedEndpointIntegral S.g1 S.g1_admissible L P.Phi hTheta
  let box : Set ReferenceEndpointVariables :=
    Icc (0 : ℝ) 1 ×ˢ ((K ×ˢ Icc (-R) R) ×ˢ closedBall (0 : R3) 1)
  have hBox : IsCompact box :=
    isCompact_Icc.prod ((hCompact.prod isCompact_Icc).prod (isCompact_closedBall _ _))
  obtain ⟨D, hD⟩ := hBox.exists_bound_of_continuousOn hQ.continuous.continuousOn
  refine ⟨max D 1, le_max_right _ _, ?_⟩
  intro lam hLam y hy r hr z hz
  have hMember : (lam, ((y, r), z)) ∈ box :=
    ⟨hLam, ⟨⟨hy.1, hr⟩, hz⟩⟩
  have hBound : ‖Q (lam, ((y, r), z))‖ ≤ max D 1 :=
    (hD _ hMember).trans (le_max_left _ _)
  have hEndpoint : packetEndpoint S L P lam y r z =
      y + r • Q (lam, ((y, r), z)) :=
    referenceFramedPhysicalEndpoint_eq_center_add_radius_integral_on_domain
      S.g1 S.g1_admissible L P.y0 P.Phi P.B hData (lam, ((y, r), z))
      ⟨hLam, (P.centers_room y hy.2).2⟩
  rw [hEndpoint, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc
    |r| * ‖Q (lam, ((y, r), z))‖ ≤ |r| * max D 1 :=
      mul_le_mul_of_nonneg_left hBound (abs_nonneg r)
    _ = max D 1 * |r| := mul_comm _ _

theorem exists_packetEndpoint_radius_bound
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i : Fin cover.count,
      ∀ lam ∈ Icc (0 : ℝ) cover.dilationCeiling,
      ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ r ∈ Icc (0 : ℝ) cover.radiusCeiling,
      ∀ z ∈ closedBall (0 : R3) 1,
        ‖packetEndpoint S L (cover.packet i) lam y r z - y‖ ≤ C * r := by
  classical
  have hPacket (i : Fin cover.count) :
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ lam ∈ Icc (0 : ℝ) 1,
        ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        ∀ r ∈ Icc (-cover.radiusCeiling) cover.radiusCeiling,
        ∀ z ∈ closedBall (0 : R3) 1,
          ‖packetEndpoint S L (cover.packet i) lam y r z - y‖ ≤ C * |r| :=
    exists_packetEndpoint_signed_radius_bound_on_compact
      S L (cover.packet i) cylinder isCompact_native_center_cylinder
      cover.radiusCeiling cover.radius_positive.le
  choose Ci hCi1 hCi using hPacket
  let C : ℝ := max 1 (∑ i : Fin cover.count, Ci i)
  have hCiNonneg (i : Fin cover.count) : 0 ≤ Ci i := zero_le_one.trans (hCi1 i)
  have hCiLe (i : Fin cover.count) : Ci i ≤ C :=
    (Finset.single_le_sum (fun j _ => hCiNonneg j) (Finset.mem_univ i)).trans
      (le_max_right _ _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro i lam hLam y hy r hr z hz
  have hLam1 : lam ∈ Icc (0 : ℝ) 1 :=
    ⟨hLam.1, hLam.2.trans cover.dilation_le_one⟩
  have hSignedRadius : r ∈ Icc (-cover.radiusCeiling) cover.radiusCeiling :=
    ⟨(neg_nonpos.mpr cover.radius_positive.le).trans hr.1, hr.2⟩
  calc
    ‖packetEndpoint S L (cover.packet i) lam y r z - y‖ ≤ Ci i * |r| :=
      hCi i lam hLam1 y hy r hSignedRadius z hz
    _ = Ci i * r := by rw [abs_of_nonneg hr.1]
    _ ≤ C * r := mul_le_mul_of_nonneg_right (hCiLe i) hr.1

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
