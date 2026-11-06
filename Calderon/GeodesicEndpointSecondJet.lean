import Calderon.GeodesicEndpoint
import Calderon.GeodesicFlowSecondJet

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

theorem exists_smooth_coordinate_spray_endpoint_secondJet (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y0 : E) :
    ∃ (Φ : (E × E) → ℝ → E × E) (A : Set (E × E)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (E × E) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ y, (y,0) ∈ A → ∀ t, Φ (y,0) t = (y,0)) ∧
      (∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ z) (geodesicPhaseField Q M (Φ z t)) t) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      (∀ y, (y,0) ∈ A → HasFDerivAt (fun z => (Φ z 1).1)
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0)) ∧
      ∀ y, (y,0) ∈ A → ∀ h k : E × E,
        fderiv ℝ (fderiv ℝ (fun z => (Φ z 1).1)) (y,0) k h =
          -(1/2 : ℝ) • (coordinateConnectionField Q M y h.2 k.2 +
            coordinateConnectionField Q M y k.2 h.2) := by
  let a : E × E := (y0,0)
  have hs : ContDiffOn ℝ (∞ + 1) (geodesicPhaseField Q M) univ := by
    simpa using (contDiff_geodesicPhaseField Q M hQ hM).contDiffOn
  obtain ⟨v,K,hvs,hv,heq⟩ :=
    hs.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
      (x := a) (by simp)
  have hvs' : ContDiff ℝ ∞ v := by simpa using hvs
  have hz : v a = 0 := by
    rw [heq.self_of_nhds]
    exact geodesicPhaseField_zero_velocity Q M y0
  have hstat := globalSolution_stationary v hv a hz
  have hF := contDiff_infty_globalSolution v hv hvs'
  obtain ⟨U,hUeq,hU,haU⟩ := mem_nhds_iff.mp heq
  have hopen : IsOpen ((fun p : (E × E) × ℝ =>
      ODE.globalSolution v hv p.1 p.2) ⁻¹' U) := hU.preimage hF.continuous
  have hsub : ({a} : Set (E × E)) ×ˢ Icc (0 : ℝ) 1 ⊆
      (fun p : (E × E) × ℝ => ODE.globalSolution v hv p.1 p.2) ⁻¹' U := by
    intro p hp
    change ODE.globalSolution v hv p.1 p.2 ∈ U
    rw [show p.1 = a from hp.1,hstat]
    exact haU
  obtain ⟨A,T,hA,_,haA,hIT,hAT⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  have hAU : A ⊆ U := by
    intro z hzA
    have hx := hAT (a := (z,0)) ⟨hzA,hIT (by simp)⟩
    simpa only [mem_preimage, ODE.globalSolution_zero] using hx
  have hzero (y : E) (hy : (y,0) ∈ A) : v (y,0) = 0 := by
    rw [hUeq (hAU hy)]
    exact geodesicPhaseField_zero_velocity Q M y
  refine ⟨ODE.globalSolution v hv,A,hA,haA (mem_singleton a),hF,
    ODE.globalSolution_zero v hv,
    fun y hy => globalSolution_stationary v hv (y,0) (hzero y hy),?_,?_,?_,?_⟩
  · intro z hzA t ht
    have hpos : ODE.globalSolution v hv z t ∈ U := hAT (a := (z,t)) ⟨hzA,hIT ht⟩
    rw [← hUeq hpos]
    exact ODE.hasDerivAt_globalSolution v hv z t
  · exact contDiff_fst.comp (hF.comp (contDiff_id.prodMk contDiff_const))
  · intro y hy
    have hlocal : v =ᶠ[𝓝 (y,0)] geodesicPhaseField Q M := by
      filter_upwards [hU.mem_nhds (hAU hy)] with z hzU
      exact hUeq hzU
    have hD : fderiv ℝ v (y,0) = zeroVelocityLinearization :=
      hlocal.fderiv_eq.trans (fderiv_geodesicPhaseField_zero_velocity Q M hQ hM y)
    exact hasFDerivAt_stationary_zeroVelocity_endpoint v hv hvs' y (hzero y hy) hD

  · intro y hy h k
    have hlocal : v =ᶠ[𝓝 (y,0)] geodesicPhaseField Q M := by
      filter_upwards [hU.mem_nhds (hAU hy)] with z hzU
      exact hUeq hzU
    have hD : fderiv ℝ v (y,0) = zeroVelocityLinearization :=
      hlocal.fderiv_eq.trans (fderiv_geodesicPhaseField_zero_velocity Q M hQ hM y)
    have hH (d e : E × E) : fderiv ℝ (fderiv ℝ v) (y,0) e d =
        (0,-(coordinateConnectionField Q M y d.2 e.2 +
          coordinateConnectionField Q M y e.2 d.2)) := by
      rw [hlocal.fderiv.fderiv_eq]
      exact fderiv_fderiv_geodesicPhaseField_zero_velocity Q M hQ hM y d e
    exact fderiv_fderiv_stationary_spray_endpoint v hv hvs' y (hzero y hy) hD
      (coordinateConnectionField Q M y) hH h k
end OAI.AnisotropicCalderon.ConnectionError
