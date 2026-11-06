import Calderon.CompactParameterReferencePositiveCoefficients
import Calderon.LocalCoefficientJetTransport
import Mathlib.Topology.Order.DenselyOrdered

/-! UNCOMPILED source-only author proposal. EXPANSION.md J1--J10 was saved before source.
All joint-flow/positive/drift parents remain disclosed as uncompiled mathematical inputs.
Raw inverse/determinant smoothness is only local at positive points. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Genuine joint germ in every variable, with strict q/center/radius/spatial neighborhood, proved from retained wide room. -/
theorem referenceCoefficientRadialReorder_eventuallyEq_on_joint_room
    (F G : (ℝ × (R3 × ℝ)) × R3 → V) (ρ : ℝ) (hρ : 0 < ρ) (y0 : R3)
    (heq : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 4*ρ →
      ∀ r : ℝ, |r| ≤ 4*ρ → ∀ z : R3, ‖z‖ ≤ 2 → F ((q,(y,r)),z) = G ((q,(y,r)),z))
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (y z : R3) (r : ℝ)
    (hy : ‖y-y0‖ < 2*ρ) (hz : ‖z‖ < 1) (hr : |r| ≤ ρ) :
    referenceCoefficientRadialReorder F =ᶠ[𝓝 ((q,(y,z)),r)]
      referenceCoefficientRadialReorder G := by
  let U : Set ((ℝ × (R3 × R3)) × ℝ) :=
    {p | p.1.1 ∈ Ioo (0 : ℝ) 1 ∧ ‖p.1.2.1-y0‖ < 4*ρ ∧
      |p.2| < 4*ρ ∧ ‖p.1.2.2‖ < 2}
  have hqOpen : IsOpen {p : (ℝ × (R3 × R3)) × ℝ | p.1.1 ∈ Ioo (0 : ℝ) 1} :=
    isOpen_Ioo.preimage continuous_fst.fst
  have hyCont : Continuous (fun p : (ℝ × (R3 × R3)) × ℝ => ‖p.1.2.1-y0‖) :=
    (continuous_fst.snd.fst.sub continuous_const).norm
  have hrCont : Continuous (fun p : (ℝ × (R3 × R3)) × ℝ => |p.2|) :=
    continuous_snd.abs
  have hzCont : Continuous (fun p : (ℝ × (R3 × R3)) × ℝ => ‖p.1.2.2‖) :=
    continuous_fst.snd.snd.norm
  have hU : IsOpen U := hqOpen.inter
    ((isOpen_lt hyCont continuous_const).inter
      ((isOpen_lt hrCont continuous_const).inter (isOpen_lt hzCont continuous_const)))
  have hp : ((q,(y,z)),r) ∈ U :=
    ⟨hq,by linarith,by linarith,by linarith⟩
  filter_upwards [hU.mem_nhds hp] with p hp
  exact heq p.1.1 ⟨hp.1.1.le,hp.1.2.le⟩ p.1.2.1 hp.2.1.le
    p.2 hp.2.2.1.le p.1.2.2 hp.2.2.2.le

/-- Relative closure of genuine ambient jets: q endpoints and full spatial boundary are included using local raw smoothness throughout closed product t. -/
theorem referenceCoefficientNonradialJet_eq_of_local_raw_smoothness
    (F G : (ℝ × (R3 × ℝ)) × R3 → V) (hF : ContDiff ℝ ∞ F)
    (ρ : ℝ) (hρ : 0 < ρ) (y0 : R3)
    (hG : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 2*ρ →
      ∀ r : ℝ, |r| ≤ ρ → ∀ z : R3, ‖z‖ ≤ 1 → ContDiffAt ℝ ∞ G ((q,(y,r)),z))
    (heq : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 4*ρ →
      ∀ r : ℝ, |r| ≤ 4*ρ → ∀ z : R3, ‖z‖ ≤ 2 → F ((q,(y,r)),z) = G ((q,(y,r)),z))
    (j : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y z : R3) (r : ℝ)
    (hy : ‖y-y0‖ ≤ ρ) (hz : ‖z‖ ≤ 1) (hr : |r| ≤ ρ) :
    parameterJetField j (referenceCoefficientRadialReorder F) ((q,(y,z)),r) =
      parameterJetField j (referenceCoefficientRadialReorder G) ((q,(y,z)),r) := by
  let s : Set (ℝ × (R3 × R3)) :=
    Ioo (0 : ℝ) 1 ×ˢ (ball y0 (2*ρ) ×ˢ ball (0 : R3) 1)
  let t : Set (ℝ × (R3 × R3)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 (2*ρ) ×ˢ closedBall (0 : R3) 1)
  have hcl : closure s = t := by
    simp only [s,t,closure_prod_eq,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_ball y0 (by positivity : 2*ρ ≠ 0),
      closure_ball (0 : R3) (by norm_num : (1 : ℝ) ≠ 0)]
  have hst : s ⊆ t := by
    intro p hp
    exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,
      ball_subset_closedBall hp.2.1,ball_subset_closedBall hp.2.2⟩
  have hts : t ⊆ closure s := by rw [hcl]
  have hc : ContDiff ℝ ∞
      (fun p : (ℝ × (R3 × R3)) × ℝ => ((p.1.1,(p.1.2.1,p.2)),p.1.2.2)) :=
    (contDiff_fst.fst.prodMk
      (contDiff_fst.snd.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd.snd
  have hlocalG : ∀ p ∈ t, ContDiffAt ℝ ∞ (referenceCoefficientRadialReorder G) (p,r) := by
    intro p hp
    have hy' : ‖p.2.1-y0‖ ≤ 2*ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    have hz' : ‖p.2.2‖ ≤ 1 := by
      simpa only [mem_closedBall,dist_zero_right] using hp.2.2
    exact (hG p.1 hp.1 p.2.1 hy' r hr p.2.2 hz').comp (p,r) hc.contDiffAt
  have he : ∀ p ∈ s, referenceCoefficientRadialReorder F =ᶠ[𝓝 (p,r)]
      referenceCoefficientRadialReorder G := by
    intro p hp
    apply referenceCoefficientRadialReorder_eventuallyEq_on_joint_room
      F G ρ hρ y0 heq p.1 hp.1 p.2.1 p.2.2 r
    · simpa only [mem_ball,dist_eq_norm] using hp.2.1
    · simpa only [mem_ball,dist_zero_right] using hp.2.2
    · exact hr
  have hclosed := parameterJetField_eq_on_set_of_local_eq j
    (referenceCoefficientRadialReorder F) (referenceCoefficientRadialReorder G)
    s t hst hts r
    (fun p _ => (contDiff_referenceCoefficientRadialReorder F hF).contDiffAt) hlocalG he
  have hp : (q,(y,z)) ∈ t := by
    refine ⟨hq,?_,?_⟩
    · simpa only [mem_closedBall,dist_eq_norm] using (by linarith : ‖y-y0‖ ≤ 2*ρ)
    · simpa only [mem_closedBall,dist_zero_right] using hz
  exact hclosed (q,(y,z)) hp

/-- Literal error fields and actual parameterJetField in q/center/spatial directions only. -/
def JointRawCoefficientMixedJetIdentities (y0 : R3) (ρ : ℝ)
    (H a G : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) : Prop :=
  ∀ j : ℕ, ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
    ∀ z : R3, ‖z‖ ≤ 1 → ∀ r : ℝ, |r| ≤ ρ →
      parameterJetField j (referenceCoefficientRadialReorder (fun x => H x-1)) ((q,(y,z)),r) =
        parameterJetField j (referenceCoefficientRadialReorder (fun x => G x-1)) ((q,(y,z)),r) ∧
      parameterJetField j (referenceCoefficientRadialReorder (fun x => a x-1)) ((q,(y,z)),r) =
        parameterJetField j (referenceCoefficientRadialReorder (fun x => matrixPrincipalCoefficient G x-1))
          ((q,(y,z)),r) ∧
      parameterJetField j (referenceCoefficientRadialReorder (fun x => w x-1)) ((q,(y,z)),r) =
        parameterJetField j (referenceCoefficientRadialReorder (fun x => matrixVolumeDensity G x-1))
          ((q,(y,z)),r)

/-- Derive raw point positivity from H=G at every closed product point; native determinant/inverse point calculus plus J2 transports all three genuine error jets. -/
theorem jointRawCoefficientMixedJetIdentities_of_geometric_room
    (H a G : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hH : ContDiff ℝ ∞ H) (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiff ℝ ∞ G) (hposH : ∀ x, (H x).PosDef)
    (ρ : ℝ) (hρ : 0 < ρ) (y0 : R3)
    (heq : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 4*ρ →
      ∀ r : ℝ, |r| ≤ 4*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
        H ((q,(y,r)),z) = G ((q,(y,r)),z) ∧
        a ((q,(y,r)),z) = matrixPrincipalCoefficient G ((q,(y,r)),z) ∧
        w ((q,(y,r)),z) = matrixVolumeDensity G ((q,(y,r)),z)) :
    JointRawCoefficientMixedJetIdentities y0 ρ H a G w := by
  have hposG : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 2*ρ →
      ∀ r : ℝ, |r| ≤ ρ → ∀ z : R3, ‖z‖ ≤ 1 → (G ((q,(y,r)),z)).PosDef := by
    intro q hq y hy r hr z hz
    rw [← (heq q hq y (by linarith) r (by linarith) z (by linarith)).1]
    exact hposH ((q,(y,r)),z)
  have hsA : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 2*ρ →
      ∀ r : ℝ, |r| ≤ ρ → ∀ z : R3, ‖z‖ ≤ 1 →
        ContDiffAt ℝ ∞ (matrixPrincipalCoefficient G) ((q,(y,r)),z) := by
    intro q hq y hy r hr z hz
    exact contDiffAt_matrixPrincipalCoefficient_of_posDef G ((q,(y,r)),z)
      hG.contDiffAt (hposG q hq y hy r hr z hz)
  have hsW : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 2*ρ →
      ∀ r : ℝ, |r| ≤ ρ → ∀ z : R3, ‖z‖ ≤ 1 →
        ContDiffAt ℝ ∞ (matrixVolumeDensity G) ((q,(y,r)),z) := by
    intro q hq y hy r hr z hz
    exact contDiffAt_matrixVolumeDensity_of_posDef G ((q,(y,r)),z)
      hG.contDiffAt (hposG q hq y hy r hr z hz)
  intro j q hq y hy z hz r hr
  refine ⟨?_,?_,?_⟩
  · exact referenceCoefficientNonradialJet_eq_of_local_raw_smoothness
      (fun x => H x-1) (fun x => G x-1) (hH.sub contDiff_const) ρ hρ y0
      (fun q _ y _ r _ z _ => hG.contDiffAt.sub contDiffAt_const)
      (fun q hq y hy r hr z hz => congrArg (fun A => A-1) (heq q hq y hy r hr z hz).1)
      j q hq y z r hy hz hr
  · exact referenceCoefficientNonradialJet_eq_of_local_raw_smoothness
      (fun x => a x-1) (fun x => matrixPrincipalCoefficient G x-1) (ha.sub contDiff_const) ρ hρ y0
      (fun q hq y hy r hr z hz => (hsA q hq y hy r hr z hz).sub contDiffAt_const)
      (fun q hq y hy r hr z hz => congrArg (fun A => A-1) (heq q hq y hy r hr z hz).2.1)
      j q hq y z r hy hz hr
  · exact referenceCoefficientNonradialJet_eq_of_local_raw_smoothness
      (fun x => w x-1) (fun x => matrixVolumeDensity G x-1) (hw.sub contDiff_const) ρ hρ y0
      (fun q hq y hy r hr z hz => (hsW q hq y hy r hr z hz).sub contDiffAt_const)
      (fun q hq y hy r hr z hz => congrArg (fun A => A-1) (heq q hq y hy r hr z hz).2.2)
      j q hq y z r hy hz hr

/-- One original radius before N, finite genuine nonradial jets of raw errors O(r²). -/
def JointRawCoefficientNonradialBounds (y0 : R3) (ρ : ℝ)
    (G : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
      ∀ z : R3, ‖z‖ ≤ 1 → ∀ r : ℝ, |r| ≤ ρ →
        ‖parameterJetField j (referenceCoefficientRadialReorder (fun x => G x-1))
          ((q,(y,z)),r)‖ ≤ D*r^2 ∧
        ‖parameterJetField j (referenceCoefficientRadialReorder
          (fun x => matrixPrincipalCoefficient G x-1)) ((q,(y,z)),r)‖ ≤ D*r^2 ∧
        ‖parameterJetField j (referenceCoefficientRadialReorder
          (fun x => matrixVolumeDensity G x-1)) ((q,(y,z)),r)‖ ≤ D*r^2

/-- Transfer exactly the existing finite-order constant D; restrict only spatial closed2 to closed1. -/
theorem jointRawCoefficientNonradialBounds_transfer (y0 : R3) (ρ : ℝ)
    (H a G : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (heq : JointRawCoefficientMixedJetIdentities y0 ρ H a G w)
    (hbound : JointReferenceCoefficientMixedBounds y0 ρ H a w) :
    JointRawCoefficientNonradialBounds y0 ρ G := by
  intro N
  obtain ⟨D,hD,hb⟩ := hbound N
  refine ⟨D,hD,?_⟩
  intro j hj q hq y hy z hz r hr
  have hp : (q,(y,z)) ∈ referenceCoefficientNonradialRoom y0 ρ := by
    refine ⟨hq,?_,?_⟩
    · simpa only [mem_closedBall,dist_eq_norm] using hy
    · simpa only [mem_closedBall,dist_zero_right] using hz.trans (by norm_num : (1 : ℝ) ≤ 2)
  have h := hb j hj (q,(y,z)) hp r hr
  rcases heq j q hq y hy z hz r hr with ⟨hH,ha,hw⟩
  rw [← hH,← ha,← hw]
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- Actual zeroth and radial first jets, transferred by a signed radial germ for fixed q, including q endpoints. -/
def JointRawCoefficientZeroRadialJets (y0 : R3) (ρ : ℝ)
    (G : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ z : R3, ‖z‖ ≤ 1 →
    G ((q,(y,0)),z) = 1 ∧ matrixPrincipalCoefficient G ((q,(y,0)),z) = 1 ∧
    matrixVolumeDensity G ((q,(y,0)),z) = 1 ∧
    HasDerivAt (fun r : ℝ => G ((q,(y,r)),z)) 0 0 ∧
    HasDerivAt (fun r : ℝ => matrixPrincipalCoefficient G ((q,(y,r)),z)) 0 0 ∧
    HasDerivAt (fun r : ℝ => matrixVolumeDensity G ((q,(y,r)),z)) 0 0

/-- Use the actual retained H/a/w radial HasDerivAt and literal fixed-q equality for all signed small radii; no q-neighbor identity is used. -/
theorem jointRawCoefficientZeroRadialJets_of_geometric_room
    (H a G : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (y0 : R3)
    (heq : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 4*ρ →
      ∀ r : ℝ, |r| ≤ 4*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
        H ((q,(y,r)),z) = G ((q,(y,r)),z) ∧
        a ((q,(y,r)),z) = matrixPrincipalCoefficient G ((q,(y,r)),z) ∧
        w ((q,(y,r)),z) = matrixVolumeDensity G ((q,(y,r)),z))
    (hzero : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ 2*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
      H ((q,(y,0)),z) = 1 ∧ a ((q,(y,0)),z) = 1 ∧ w ((q,(y,0)),z) = 1 ∧
      HasDerivAt (fun r : ℝ => H ((q,(y,r)),z)) 0 0 ∧
      HasDerivAt (fun r : ℝ => a ((q,(y,r)),z)) 0 0 ∧
      HasDerivAt (fun r : ℝ => w ((q,(y,r)),z)) 0 0) :
    JointRawCoefficientZeroRadialJets y0 ρ G := by
  intro q hq y hy z hz
  have hy4 : ‖y-y0‖ ≤ 4*ρ := by linarith
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith
  have hz2 : ‖z‖ ≤ 2 := by linarith
  have h0 := heq q hq y hy4 0 (by simpa using (by positivity : 0 ≤ 4*ρ)) z hz2
  have hZ := hzero q hq y hy2 z hz2
  have hE : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ),
      H ((q,(y,r)),z) = G ((q,(y,r)),z) ∧
      a ((q,(y,r)),z) = matrixPrincipalCoefficient G ((q,(y,r)),z) ∧
      w ((q,(y,r)),z) = matrixVolumeDensity G ((q,(y,r)),z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with r hr
    have hr' : |r| < ρ := by
      simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hr
    exact heq q hq y hy4 r (by linarith) z hz2
  have hEH : (fun r : ℝ => G ((q,(y,r)),z)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => H ((q,(y,r)),z)) := by
    filter_upwards [hE] with r hr
    exact hr.1.symm
  have hEA : (fun r : ℝ => matrixPrincipalCoefficient G ((q,(y,r)),z)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => a ((q,(y,r)),z)) := by
    filter_upwards [hE] with r hr
    exact hr.2.1.symm
  have hEW : (fun r : ℝ => matrixVolumeDensity G ((q,(y,r)),z)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => w ((q,(y,r)),z)) := by
    filter_upwards [hE] with r hr
    exact hr.2.2.symm
  exact ⟨h0.1.symm.trans hZ.1,h0.2.1.symm.trans hZ.2.1,h0.2.2.symm.trans hZ.2.2.1,
    hZ.2.2.2.1.congr_of_eventuallyEq hEH,
    hZ.2.2.2.2.1.congr_of_eventuallyEq hEA,
    hZ.2.2.2.2.2.congr_of_eventuallyEq hEW⟩

end OAI.AnisotropicCalderon.ConnectionError
