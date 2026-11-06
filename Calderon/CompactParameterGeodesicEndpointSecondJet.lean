import Calderon.CompactParameterGeodesicFlowJets

/-! The explicit one-cutoff construction retains the joint room
and appends jets of the very same augmented global flow. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

theorem exists_smooth_parameter_geodesic_endpoint_secondJet
    (Q M : P × E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (K : Set P) (hK : IsCompact K) (y0 : E) :
    ∃ (Φ : P → (E × E) → ℝ → E × E) (B : Set (E × E)),
      IsOpen B ∧ (y0,0) ∈ B ∧
      ContDiff ℝ ∞ (fun p : (P × (E × E)) × ℝ => Φ p.1.1 p.1.2 p.2) ∧
      (∀ q z, Φ q z 0 = z) ∧
      (∀ q z t u, Φ q z (t + u) = Φ q (Φ q z t) u) ∧
      (∀ q ∈ K, ∀ y, (y,0) ∈ B → ∀ t, Φ q (y,0) t = (y,0)) ∧
      (∀ q ∈ K, ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ q z)
          (geodesicPhaseField (fun y => Q (q,y)) (fun y => M (q,y)) (Φ q z t)) t) ∧
      ContDiff ℝ ∞ (fun p : P × (E × E) => (Φ p.1 p.2 1).1) ∧
      (∀ q ∈ K, ∀ y, (y,0) ∈ B → (Φ q (y,0) 1).1 = y) ∧
      (∀ q ∈ K, ∀ y, (y,0) ∈ B →
        HasFDerivAt (fun z => (Φ q z 1).1)
          (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0)) ∧
      ∀ q ∈ K, ∀ y, (y,0) ∈ B → ∀ h k : E × E,
        fderiv ℝ (fderiv ℝ (fun z => (Φ q z 1).1)) (y,0) k h =
          -(1/2 : ℝ) • (parameterCoordinateConnectionField Q M (q,y) h.2 k.2 +
            parameterCoordinateConnectionField Q M (q,y) k.2 h.2) := by
  let H := parameterGeodesicPhaseField Q M
  let C : Set (P × (E × E)) := K ×ˢ {(y0,0)}
  have hC : IsCompact C := hK.prod isCompact_singleton
  obtain ⟨W,L,U,hWs,hcomp,hW,hU,hCU,hEq,hWfst⟩ :=
    exists_compact_supported_parameter_preserving_extension H
      (contDiff_parameterGeodesicPhaseField Q M hQ hM)
      (parameterGeodesicPhaseField_fst Q M) C hC
  let F : (P × (E × E)) → ℝ → P × (E × E) := ODE.globalSolution W hW
  have hF : ContDiff ℝ ∞ (fun p : (P × (E × E)) × ℝ => F p.1 p.2) :=
    contDiff_infty_globalSolution W hW hWs
  have hstat0 (q : P) (hq : q ∈ K) : ∀ t, F (q,(y0,0)) t = (q,(y0,0)) := by
    have hz : W (q,(y0,0)) = 0 :=
      (hEq (hCU ⟨hq,mem_singleton (y0,0)⟩)).trans
        (parameterGeodesicPhaseField_zero_velocity Q M q y0)
    exact globalSolution_stationary W hW (q,(y0,0)) hz
  have hopen : IsOpen ((fun p : (P × (E × E)) × ℝ => F p.1 p.2) ⁻¹' U) :=
    hU.preimage hF.continuous
  have hsub : C ×ˢ Icc (0 : ℝ) 1 ⊆
      (fun p : (P × (E × E)) × ℝ => F p.1 p.2) ⁻¹' U := by
    rintro ⟨⟨q,z⟩,t⟩ ⟨⟨hq,hz⟩,ht⟩
    have hz' : z = (y0,0) := hz
    subst z
    change F (q,(y0,0)) t ∈ U
    rw [hstat0 q hq]
    exact hCU ⟨hq,mem_singleton (y0,0)⟩
  obtain ⟨A,T,hA,hT,hCA,hIT,hAT⟩ :=
    generalized_tube_lemma hC isCompact_Icc hopen hsub
  have hAU : A ⊆ U := by
    intro z hz
    have hx := hAT (a := (z,0)) ⟨hz,hIT (by simp)⟩
    simpa only [mem_preimage,F,ODE.globalSolution_zero] using hx
  obtain ⟨O,B,hO,hB,hKO,haB,hOB⟩ :=
    generalized_tube_lemma hK isCompact_singleton hA hCA
  let Φ : P → (E × E) → ℝ → E × E := fun q z t => (F (q,z) t).2
  have hpair (q : P) (z : E × E) (t : ℝ) : F (q,z) t = (q,Φ q z t) := by
    apply Prod.ext
    · exact globalSolution_parameter_eq W hW hWfst q z t
    · rfl
  have hlocal (q : P) (hq : q ∈ K) (y : E) (hy : (y,0) ∈ B) :
      W =ᶠ[𝓝 (q,(y,0))] H := by
    filter_upwards [hU.mem_nhds (hAU (hOB ⟨hKO hq,hy⟩))] with z hz
    exact hEq hz
  have hzero (q : P) (hq : q ∈ K) (y : E) (hy : (y,0) ∈ B) : W (q,(y,0)) = 0 :=
    (hlocal q hq y hy).self_of_nhds.trans
      (parameterGeodesicPhaseField_zero_velocity Q M q y)
  have hD (q : P) (hq : q ∈ K) (y : E) (hy : (y,0) ∈ B) :
      fderiv ℝ W (q,(y,0)) = parameterZeroVelocityLinearization :=
    (hlocal q hq y hy).fderiv_eq.trans
      (fderiv_parameterGeodesicPhaseField_zero_velocity Q M hQ hM q y)
  have hH (q : P) (hq : q ∈ K) (y : E) (hy : (y,0) ∈ B)
      (d e : P × (E × E)) :
      fderiv ℝ (fderiv ℝ W) (q,(y,0)) e d =
        (0,(0,-(parameterCoordinateConnectionField Q M (q,y) d.2.2 e.2.2 +
          parameterCoordinateConnectionField Q M (q,y) e.2.2 d.2.2))) := by
    rw [(hlocal q hq y hy).fderiv.fderiv_eq]
    exact fderiv_fderiv_parameterGeodesicPhaseField_zero_velocity Q M hQ hM q y d e
  refine ⟨Φ,B,hB,haB (mem_singleton (y0,0)),contDiff_snd.comp hF,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro q z
    exact congrArg Prod.snd (ODE.globalSolution_zero W hW (q,z))
  · intro q z t u
    have hflow := ODE.globalSolution_add W hW (q,z) t u
    change F (q,z) (t + u) = F (F (q,z) t) u at hflow
    rw [hpair q z t] at hflow
    exact congrArg Prod.snd hflow
  · intro q hq y hy t
    exact congrArg Prod.snd (globalSolution_stationary W hW (q,(y,0)) (hzero q hq y hy) t)
  · intro q hq z hz t ht
    have hpos : F (q,z) t ∈ U := hAT (a := ((q,z),t))
      ⟨hOB ⟨hKO hq,hz⟩,hIT ht⟩
    have hd := (ODE.hasDerivAt_globalSolution W hW (q,z) t).snd
    change HasDerivAt (fun s => (F (q,z) s).2) (W (F (q,z) t)).2 t at hd
    rw [hEq hpos,hpair q z t] at hd
    exact hd
  · exact contDiff_fst.comp ((contDiff_snd.comp hF).comp (contDiff_id.prodMk contDiff_const))
  · intro q hq y hy
    exact congrArg (fun z : P × (E × E) => z.2.1)
      (globalSolution_stationary W hW (q,(y,0)) (hzero q hq y hy) 1)
  · intro q hq y hy
    exact hasFDerivAt_parameter_stationary_zeroVelocity_endpoint
      W hW hWs q y (hzero q hq y hy) (hD q hq y hy)
  · intro q hq y hy h k
    exact fderiv_fderiv_parameter_stationary_spray_endpoint
      W hW hWs q y (hzero q hq y hy) (hD q hq y hy)
      (parameterCoordinateConnectionField Q M (q,y)) (hH q hq y hy) h k
end OAI.AnisotropicCalderon.ConnectionError
