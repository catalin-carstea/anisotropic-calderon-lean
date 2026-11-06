import Calderon.SmoothGeodesicFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact

/-!
A compact-parameter flow: one compactly supported parameter-preserving field and one
global flow are used.
-/
set_option autoImplicit false
noncomputable section
open Filter Set Metric
open scoped ContDiff Topology NNReal
namespace OAI.AnisotropicCalderon.ConnectionError

section ParameterPreserving
variable {P S : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- A single compact-supported extension on a compact set preserves a zero
parameter component by construction. -/
theorem exists_compact_supported_parameter_preserving_extension
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ S]
    (H : P × S → P × S) (hH : ContDiff ℝ ∞ H)
    (hfst : ∀ a, (H a).1 = 0) (C : Set (P × S)) (hC : IsCompact C) :
    ∃ (V : P × S → P × S) (L : ℝ≥0) (U : Set (P × S)),
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧ LipschitzWith L V ∧
      IsOpen U ∧ C ⊆ U ∧ EqOn V H U ∧ ∀ a, (V a).1 = 0 := by
  obtain ⟨R,hR,hCR⟩ := hC.isBounded.exists_pos_norm_lt
  let b : ContDiffBump (0 : P × S) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  let V : P × S → P × S := fun a => b a • H a
  let U : Set (P × S) := ball 0 R
  have hV : ContDiff ℝ ∞ V := b.contDiff.smul hH
  have hcomp : HasCompactSupport V := b.hasCompactSupport.smul_right
  obtain ⟨L,hLip⟩ := hV.lipschitzWith_of_hasCompactSupport hcomp (by simp)
  refine ⟨V,L,U,hV,hcomp,hLip,isOpen_ball,?_,?_,?_⟩
  · intro a ha
    simpa only [U,mem_ball,dist_zero_right] using hCR a ha
  · intro a ha
    have hb : b a = 1 := b.one_of_mem_closedBall (ball_subset_closedBall ha)
    simp only [V,hb,one_smul]
  · intro a
    change b a • (H a).1 = 0
    rw [hfst,smul_zero]

variable [CompleteSpace P] [CompleteSpace S]

/-- The parameter coordinate of the actual chosen global flow is constant. -/
theorem globalSolution_parameter_eq (V : P × S → P × S) {L : ℝ≥0}
    (hV : LipschitzWith L V) (hfst : ∀ a, (V a).1 = 0)
    (q : P) (z : S) (t : ℝ) :
    (ODE.globalSolution V hV (q,z) t).1 = q := by
  have hd (s : ℝ) : HasDerivAt
      (fun r => (ODE.globalSolution V hV (q,z) r).1) (0 : P) s := by
    simpa only [ContinuousLinearMap.coe_fst', Function.comp_def, hfst] using
      (ContinuousLinearMap.fst ℝ P S).hasFDerivAt.comp_hasDerivAt s
        (ODE.hasDerivAt_globalSolution V hV (q,z) s)
  have hc := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [ODE.globalSolution_zero] using hc

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ S]

/-- A compact family of stationary points has one common open initial phase
room for the actual equation on the unit interval. -/
theorem exists_smooth_parameter_preserving_flow_on_unit_interval
    (H : P × S → P × S) (hH : ContDiff ℝ ∞ H)
    (hfst : ∀ a, (H a).1 = 0)
    (K : Set P) (hK : IsCompact K) (a0 : S)
    (hzero : ∀ q ∈ K, H (q,a0) = 0) :
    ∃ (Φ : P → S → ℝ → S) (B : Set S),
      IsOpen B ∧ a0 ∈ B ∧
      ContDiff ℝ ∞ (fun p : (P × S) × ℝ => Φ p.1.1 p.1.2 p.2) ∧
      (∀ q z, Φ q z 0 = z) ∧
      (∀ q z t u, Φ q z (t + u) = Φ q (Φ q z t) u) ∧
      (∀ q ∈ K, ∀ z ∈ B, H (q,z) = 0 → ∀ t, Φ q z t = z) ∧
      ∀ q ∈ K, ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ q z) (H (q,Φ q z t)).2 t := by
  let C : Set (P × S) := K ×ˢ {a0}
  have hC : IsCompact C := hK.prod isCompact_singleton
  obtain ⟨V,L,U,hVs,hcomp,hV,hU,hCU,hEq,hVfst⟩ :=
    exists_compact_supported_parameter_preserving_extension H hH hfst C hC
  let F : (P × S) → ℝ → P × S := ODE.globalSolution V hV
  have hF : ContDiff ℝ ∞ (fun p : (P × S) × ℝ => F p.1 p.2) :=
    contDiff_infty_globalSolution V hV hVs
  have hstat (q : P) (hq : q ∈ K) : ∀ t, F (q,a0) t = (q,a0) := by
    have hz : V (q,a0) = 0 :=
      (hEq (hCU ⟨hq,mem_singleton a0⟩)).trans (hzero q hq)
    exact globalSolution_stationary V hV (q,a0) hz
  have hopen : IsOpen ((fun p : (P × S) × ℝ => F p.1 p.2) ⁻¹' U) :=
    hU.preimage hF.continuous
  have hsub : C ×ˢ Icc (0 : ℝ) 1 ⊆
      (fun p : (P × S) × ℝ => F p.1 p.2) ⁻¹' U := by
    rintro ⟨⟨q,z⟩,t⟩ ⟨⟨hq,hz⟩,ht⟩
    have hz' : z = a0 := hz
    subst z
    change F (q,a0) t ∈ U
    rw [hstat q hq]
    exact hCU ⟨hq,mem_singleton a0⟩
  obtain ⟨A,T,hA,hT,hCA,hIT,hAT⟩ :=
    generalized_tube_lemma hC isCompact_Icc hopen hsub
  have hAU : A ⊆ U := by
    intro z hz
    have hx := hAT (a := (z,0)) ⟨hz,hIT (by simp)⟩
    simpa only [mem_preimage,F,ODE.globalSolution_zero] using hx
  obtain ⟨O,B,hO,hB,hKO,haB,hOB⟩ :=
    generalized_tube_lemma hK isCompact_singleton hA hCA
  let Φ : P → S → ℝ → S := fun q z t => (F (q,z) t).2
  have hpair (q : P) (z : S) (t : ℝ) : F (q,z) t = (q,Φ q z t) := by
    apply Prod.ext
    · exact globalSolution_parameter_eq V hV hVfst q z t
    · rfl
  refine ⟨Φ,B,hB,haB (mem_singleton a0),contDiff_snd.comp hF,?_,?_,?_,?_⟩
  · intro q z
    exact congrArg Prod.snd (ODE.globalSolution_zero V hV (q,z))
  · intro q z t u
    have hflow := ODE.globalSolution_add V hV (q,z) t u
    change F (q,z) (t + u) = F (F (q,z) t) u at hflow
    rw [hpair q z t] at hflow
    exact congrArg Prod.snd hflow
  · intro q hq z hz hz0 t
    have hzU : (q,z) ∈ U := hAU (hOB ⟨hKO hq,hz⟩)
    have hzV : V (q,z) = 0 := (hEq hzU).trans hz0
    exact congrArg Prod.snd (globalSolution_stationary V hV (q,z) hzV t)
  · intro q hq z hz t ht
    have hpos : F (q,z) t ∈ U := hAT (a := ((q,z),t))
      ⟨hOB ⟨hKO hq,hz⟩,hIT ht⟩
    have hd := (ODE.hasDerivAt_globalSolution V hV (q,z) t).snd
    change HasDerivAt (fun s => (F (q,z) s).2) (V (F (q,z) t)).2 t at hd
    rw [hEq hpos,hpair q z t] at hd
    exact hd
end ParameterPreserving

section Geodesic
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The existing coordinate connection, with the parameter frozen for the
spatial derivative. -/
def parameterCoordinateConnectionField (Q M : P × E → E →L[ℝ] E) :
    P × E → E →L[ℝ] E →L[ℝ] E :=
  fun p => coordinateConnectionField (fun y => Q (p.1,y))
    (fun y => M (p.1,y)) p.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem contDiff_parameterCoordinateConnectionField
    (Q M : P × E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (parameterCoordinateConnectionField Q M) := by
  have hMf : ContDiff ℝ ∞
      (Function.uncurry (fun p : P × E => fun y : E => M (p.1,y))) :=
    hM.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hD : ContDiff ℝ ∞
      (fun p : P × E => fderiv ℝ (fun y => M (p.1,y)) p.2) :=
    hMf.fderiv contDiff_snd (by simp)
  let T : (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) :=
    koszulLinearMap (E := E)
  have hKos : ContDiff ℝ ∞
      (fun p : P × E => T (fderiv ℝ (fun y => M (p.1,y)) p.2)) := by
    simpa only [Function.comp_def] using
      (ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := E →L[ℝ] E →L[ℝ] E) (F := E →L[ℝ] E →L[ℝ] E) (n := ∞) T).comp hD
  have hComp := ((ContinuousLinearMap.compL ℝ E E E).contDiff.comp hQ).clm_comp hKos
  exact hComp.const_smul (1/2 : ℝ)

def parameterGeodesicPhaseField (Q M : P × E → E →L[ℝ] E) :
    P × (E × E) → P × (E × E) :=
  fun p => (0,(p.2.2,-parameterCoordinateConnectionField Q M (p.1,p.2.1) p.2.2 p.2.2))

theorem parameterGeodesicPhaseField_eq (Q M : P × E → E →L[ℝ] E)
    (q : P) (z : E × E) :
    parameterGeodesicPhaseField Q M (q,z) =
      (0,geodesicPhaseField (fun y => Q (q,y)) (fun y => M (q,y)) z) := rfl

theorem contDiff_parameterGeodesicPhaseField (Q M : P × E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (parameterGeodesicPhaseField Q M) := by
  have hΓ := (contDiff_parameterCoordinateConnectionField Q M hQ hM).comp
    (contDiff_fst.prodMk contDiff_snd.fst :
      ContDiff ℝ ∞ (fun p : P × (E × E) => (p.1,p.2.1)))
  have hV : ContDiff ℝ ∞ (fun p : P × (E × E) => p.2.2) := contDiff_snd.snd
  exact contDiff_const.prodMk (hV.prodMk ((hΓ.clm_apply hV).clm_apply hV).neg)

theorem parameterGeodesicPhaseField_fst (Q M : P × E → E →L[ℝ] E)
    (p : P × (E × E)) : (parameterGeodesicPhaseField Q M p).1 = 0 := rfl

theorem parameterGeodesicPhaseField_zero_velocity (Q M : P × E → E →L[ℝ] E)
    (q : P) (y : E) : parameterGeodesicPhaseField Q M (q,(y,0)) = 0 := by
  simp [parameterGeodesicPhaseField]

variable [CompleteSpace P] [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

/-- One jointly smooth family and one phase room work for every parameter in
K, with the exact frozen-slice geodesic equation and stationary endpoint. -/
theorem exists_smooth_parameter_geodesic_flow_on_unit_interval
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
      ∀ q ∈ K, ∀ y, (y,0) ∈ B → (Φ q (y,0) 1).1 = y := by
  obtain ⟨Φ,B,hB,hy0,hΦ,hinit,hadd,hstat,hODE⟩ :=
    exists_smooth_parameter_preserving_flow_on_unit_interval
      (parameterGeodesicPhaseField Q M)
      (contDiff_parameterGeodesicPhaseField Q M hQ hM)
      (parameterGeodesicPhaseField_fst Q M) K hK (y0,0)
      (fun q _ => parameterGeodesicPhaseField_zero_velocity Q M q y0)
  refine ⟨Φ,B,hB,hy0,hΦ,hinit,hadd,?_,?_,?_,?_⟩
  · intro q hq y hy t
    exact hstat q hq (y,0) hy (parameterGeodesicPhaseField_zero_velocity Q M q y) t
  · intro q hq z hz t ht
    simpa only [parameterGeodesicPhaseField_eq] using hODE q hq z hz t ht
  · exact contDiff_fst.comp (hΦ.comp (contDiff_id.prodMk contDiff_const))
  · intro q hq y hy
    exact congrArg Prod.fst
      (hstat q hq (y,0) hy (parameterGeodesicPhaseField_zero_velocity Q M q y) 1)
end Geodesic
end OAI.AnisotropicCalderon.ConnectionError
