import Calderon.ParameterFramedNormalizedEndpoint
import Calderon.NormalizedConformalDrift
import Calderon.WeightedRadialDriftCoercivity
import Calderon.JointParameterFiberChart

/-! All parameter slices and normalized endpoint derivatives are literal native definitions. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise BigOperators
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator DirichletFamily
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def parameterFramedScaledEndpoint (Θ : P × (R3 × R3) → R3)
    (F : P × R3 → R3 →L[ℝ] R3) (p : (P × (R3 × ℝ)) × R3) : R3 :=
  framedScaledEndpoint (fun z => Θ (p.1.1,z)) (fun y => F (p.1.1,y)) (p.1.2,p.2)

def parameterFramedNormalizedEndpointDerivative (Θ : P × (R3 × R3) → R3)
    (F : P × R3 → R3 →L[ℝ] R3) (p : (P × (R3 × ℝ)) × R3) : R3 →L[ℝ] R3 :=
  framedNormalizedEndpointDerivative (fun z => Θ (p.1.1,z))
    (fun y => F (p.1.1,y)) (p.1.2,p.2)

theorem contDiff_parameterFramedScaledEndpoint
    (Θ : P × (R3 × R3) → R3) (F : P × R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterFramedScaledEndpoint Θ F) := by
  have hA : ContDiff ℝ ∞ (fun p : (P × (R3 × ℝ)) × R3 => F (p.1.1,p.1.2.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_fst.snd.fst)
  change ContDiff ℝ ∞ (fun p : (P × (R3 × ℝ)) × R3 =>
    Θ (p.1.1,(p.1.2.1,p.1.2.2 • F (p.1.1,p.1.2.1) p.2)))
  exact hΘ.comp (contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.smul (hA.clm_apply contDiff_snd))))

theorem contDiff_parameterFramedNormalizedEndpointDerivative
    (Θ : P × (R3 × R3) → R3) (F : P × R3 → R3 →L[ℝ] R3)
    (hΘ : ContDiff ℝ ∞ Θ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterFramedNormalizedEndpointDerivative Θ F) := by
  let A : (P × (R3 × ℝ)) × R3 → R3 →L[ℝ] R3 := fun p => F (p.1.1,p.1.2.1)
  let T : (P × (R3 × ℝ)) × R3 → P × (R3 × R3) :=
    fun p => (p.1.1,(p.1.2.1,p.1.2.2 • A p p.2))
  have hA : ContDiff ℝ ∞ A := hF.comp (contDiff_fst.fst.prodMk contDiff_fst.snd.fst)
  have hT : ContDiff ℝ ∞ T := contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.smul (hA.clm_apply contDiff_snd)))
  have heq : parameterFramedNormalizedEndpointDerivative Θ F = fun p =>
      ((parameterPhaseDerivative Θ (T p)).comp (ContinuousLinearMap.inr ℝ R3 R3)).comp (A p) := by
    funext p
    unfold parameterFramedNormalizedEndpointDerivative framedNormalizedEndpointDerivative
      normalizedEndpointDerivative framedEndpointParameter
    rw [fderiv_parameter_endpoint_slice Θ hΘ]
  rw [heq]
  exact (((contDiff_parameterPhaseDerivative Θ hΘ).comp hT).clm_comp contDiff_const).clm_comp hA

def parameterNormalizedConformalDriftBase
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Θ : P × (R3 × R3) → R3) (F : P × R3 → R3 →L[ℝ] R3)
    (p : (P × (R3 × ℝ)) × R3) : R3 :=
  normalizedConformalDriftBase (fun s => H ((p.1.1,s.1),s.2))
    (fun z => Θ (p.1.1,z)) (fun y => F (p.1.1,y)) (p.1.2,p.2)

def parameterNormalizedConformalDrift
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Θ : P × (R3 × R3) → R3) (F : P × R3 → R3 →L[ℝ] R3) (L : ℝ)
    (p : (P × (R3 × ℝ)) × R3) : R3 :=
  normalizedConformalDrift (fun s => H ((p.1.1,s.1),s.2))
    (fun z => Θ (p.1.1,z)) (fun y => F (p.1.1,y)) L (p.1.2,p.2)

def parameterWeightedNormalizedConformalDrift
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Θ : P × (R3 × R3) → R3) (F : P × R3 → R3 →L[ℝ] R3)
    (w : (P × (R3 × ℝ)) × R3 → ℝ) (L : ℝ)
    (p : (P × (R3 × ℝ)) × R3) : R3 :=
  w p • parameterNormalizedConformalDrift H Θ F L p

theorem contDiff_parameterNormalizedConformalDriftBase
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hpos : ∀ p, (H p).PosDef)
    (Θ : P × (R3 × R3) → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (F : P × R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterNormalizedConformalDriftBase H Θ F) := by
  have hAdj : ContDiff ℝ ∞ (fun A : R3 →L[ℝ] R3 => A.adjoint) :=
    (ContinuousLinearMap.adjoint : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3)).contDiff
  exact (matrixOperatorMap.contDiff.comp (contDiff_matrixFamily_inverse H hH hpos)).clm_apply
    ((hAdj.comp (contDiff_parameterFramedNormalizedEndpointDerivative Θ F hΘ hF)).clm_apply
      (contDiff_conformalReferenceDepthGradient.comp (contDiff_parameterFramedScaledEndpoint Θ F hΘ hF)))

theorem contDiff_parameterNormalizedConformalDrift
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hpos : ∀ p, (H p).PosDef)
    (Θ : P × (R3 × R3) → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (F : P × R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F) (L : ℝ) :
    ContDiff ℝ ∞ (parameterNormalizedConformalDrift H Θ F L) := by
  exact (contDiff_const.mul contDiff_fst.snd.snd).smul
    (contDiff_parameterNormalizedConformalDriftBase H hH hpos Θ hΘ F hF)

theorem contDiff_parameterWeightedNormalizedConformalDrift
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hpos : ∀ p, (H p).PosDef)
    (Θ : P × (R3 × R3) → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (F : P × R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F)
    (w : (P × (R3 × ℝ)) × R3 → ℝ) (hw : ContDiff ℝ ∞ w) (L : ℝ) :
    ContDiff ℝ ∞ (parameterWeightedNormalizedConformalDrift H Θ F w L) := by
  exact hw.smul (contDiff_parameterNormalizedConformalDrift H hH hpos Θ hΘ F hF L)

theorem parameterNormalizedConformalDrift_zero
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Θ : P × (R3 × R3) → R3) (F : P × R3 → R3 →L[ℝ] R3)
    (w : (P × (R3 × ℝ)) × R3 → ℝ) (L : ℝ) (q : P) (y z : R3) :
    parameterNormalizedConformalDrift H Θ F L ((q,(y,0)),z) = 0 ∧
    parameterWeightedNormalizedConformalDrift H Θ F w L ((q,(y,0)),z) = 0 := by
  simp [parameterNormalizedConformalDrift,parameterWeightedNormalizedConformalDrift,
    normalizedConformalDrift]

theorem hasDerivAt_parameterNormalizedConformalDrift_zero
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hpos : ∀ p, (H p).PosDef)
    (Θ : P × (R3 × R3) → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (F : P × R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F)
    (w : (P × (R3 × ℝ)) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (L : ℝ) (q : P) (y z : R3) :
    HasDerivAt (fun r : ℝ => parameterNormalizedConformalDrift H Θ F L ((q,(y,r)),z))
      (-L • parameterNormalizedConformalDriftBase H Θ F ((q,(y,0)),z)) 0 ∧
    HasDerivAt (fun r : ℝ => parameterWeightedNormalizedConformalDrift H Θ F w L ((q,(y,r)),z))
      (-L • (w ((q,(y,0)),z) • parameterNormalizedConformalDriftBase H Θ F ((q,(y,0)),z))) 0 := by
  let Hq : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ := fun s => H ((q,s.1),s.2)
  have hHq : ContDiff ℝ ∞ Hq :=
    hH.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hThetaq : ContDiff ℝ ∞ (fun a => Θ (q,a)) :=
    hΘ.comp (contDiff_const.prodMk contDiff_id)
  have hFq : ContDiff ℝ ∞ (fun a => F (q,a)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hd := hasDerivAt_normalizedConformalDrift_zero Hq hHq
    (fun s => hpos ((q,s.1),s.2)) (fun a => Θ (q,a)) hThetaq
    (fun a => F (q,a)) hFq L y z
  refine ⟨hd,?_⟩
  have hB : ContDiff ℝ ∞ (fun r : ℝ =>
      w ((q,(y,r)),z) • parameterNormalizedConformalDriftBase H Θ F ((q,(y,r)),z)) :=
    (hw.smul (contDiff_parameterNormalizedConformalDriftBase H hH hpos Θ hΘ F hF)).comp
      ((contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).prodMk contDiff_const)
  have hbeta := ((hasDerivAt_id (0 : ℝ)).fun_smul
    ((hB.differentiable (by simp) 0).hasDerivAt)).fun_const_smul (-L)
  simpa only [parameterWeightedNormalizedConformalDrift,parameterNormalizedConformalDrift,
    normalizedConformalDrift,parameterNormalizedConformalDriftBase,Pi.smul_apply,
    smul_smul,zero_smul,one_smul,zero_add,id_eq,one_mul,mul_one,
    mul_comm,mul_left_comm,mul_assoc] using hbeta

theorem parameterNormalizedConformalDrift_local_metric_identity
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hpos : ∀ p, (H p).PosDef) (Θ : P × (R3 × R3) → R3)
    (M F : P × R3 → R3 →L[ℝ] R3) (L : ℝ) (p : (P × (R3 × ℝ)) × R3)
    (heq : H p = operatorMatrixMap
      (parameterFramedNormalizedEndpointMetric Θ M F (p.1.1,(p.1.2,p.2)))) :
    parameterFramedNormalizedEndpointMetric Θ M F (p.1.1,(p.1.2,p.2))
      (parameterNormalizedConformalDrift H Θ F L p) =
      (-L*p.1.2.2) • ((parameterFramedNormalizedEndpointDerivative Θ F p).adjoint
        (gradient conformalReferenceCoordinateDepth (parameterFramedScaledEndpoint Θ F p))) := by
  exact normalizedConformalDrift_local_metric_identity
    (fun s => H ((p.1.1,s.1),s.2)) (fun s => hpos ((p.1.1,s.1),s.2))
    (fun z => Θ (p.1.1,z)) (fun y => M (p.1.1,y)) (fun y => F (p.1.1,y))
    L (p.1.2,p.2) heq

theorem exists_compact_parameterNormalizedConformalDrift_bounds
    (H : (P × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hH : ContDiff ℝ ∞ H) (hpos : ∀ p, (H p).PosDef)
    (Θ : P × (R3 × R3) → R3) (hΘ : ContDiff ℝ ∞ Θ)
    (F : P × R3 → R3 →L[ℝ] R3) (hF : ContDiff ℝ ∞ F)
    (w : (P × (R3 × ℝ)) × R3 → ℝ) (hw : ContDiff ℝ ∞ w) (L : ℝ)
    (S : Set ((P × (R3 × ℝ)) × R3)) (hS : IsCompact S) :
    ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      (∀ j : ℕ, j ≤ N → ∀ p ∈ S,
        ‖iteratedFDeriv ℝ j (parameterNormalizedConformalDriftBase H Θ F) p‖ ≤ D ∧
        ‖iteratedFDeriv ℝ j (parameterNormalizedConformalDrift H Θ F L) p‖ ≤ D ∧
        ‖iteratedFDeriv ℝ j (parameterWeightedNormalizedConformalDrift H Θ F w L) p‖ ≤ D) ∧
      ∀ p ∈ S,
        ‖parameterNormalizedConformalDrift H Θ F L p‖ ≤ D*|p.1.2.2| ∧
        ‖parameterWeightedNormalizedConformalDrift H Θ F w L p‖ ≤ D*|p.1.2.2| := by
  let b := parameterNormalizedConformalDriftBase H Θ F
  let d := parameterNormalizedConformalDrift H Θ F L
  let beta := parameterWeightedNormalizedConformalDrift H Θ F w L
  have hb : ContDiff ℝ ∞ b := contDiff_parameterNormalizedConformalDriftBase H hH hpos Θ hΘ F hF
  have hd : ContDiff ℝ ∞ d := contDiff_parameterNormalizedConformalDrift H hH hpos Θ hΘ F hF L
  have he : ContDiff ℝ ∞ beta := contDiff_parameterWeightedNormalizedConformalDrift H hH hpos Θ hΘ F hF w hw L
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hb.continuous.continuousOn
  obtain ⟨W,hW⟩ := hS.exists_bound_of_continuousOn (hw.smul hb).continuous.continuousOn
  let K : ℝ := max B 0 + max W 0
  have hK : 0 ≤ K := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hbK : ∀ p ∈ S, ‖b p‖ ≤ K := by
    intro p hp
    exact (hB p hp).trans (by dsimp [K]; linarith [le_max_left B 0,le_max_right W 0])
  have hwK : ∀ p ∈ S, ‖w p • b p‖ ≤ K := by
    intro p hp
    exact (hW p hp).trans (by dsimp [K]; linarith [le_max_left W 0,le_max_right B 0])
  intro N
  obtain ⟨Cb,hCb,hbb⟩ := exists_compact_uniform_iteratedFDeriv_bound_on_open b Set.univ isOpen_univ
    hb.contDiffOn S hS (subset_univ S) N
  obtain ⟨Cd,hCd,hbd⟩ := exists_compact_uniform_iteratedFDeriv_bound_on_open d Set.univ isOpen_univ
    hd.contDiffOn S hS (subset_univ S) N
  obtain ⟨Ce,hCe,hbe⟩ := exists_compact_uniform_iteratedFDeriv_bound_on_open beta Set.univ isOpen_univ
    he.contDiffOn S hS (subset_univ S) N
  let D : ℝ := Cb+Cd+Ce+|L| * K
  have hLine : 0 ≤ |L| * K := mul_nonneg (abs_nonneg _) hK
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hCbD : Cb ≤ D := by dsimp [D]; linarith
  have hCdD : Cd ≤ D := by dsimp [D]; linarith
  have hCeD : Ce ≤ D := by dsimp [D]; linarith
  have hLineD : |L| * K ≤ D := by dsimp [D]; linarith
  refine ⟨D,hD,?_,?_⟩
  · intro j hj p hp
    exact ⟨(hbb j hj p hp).trans hCbD,(hbd j hj p hp).trans hCdD,(hbe j hj p hp).trans hCeD⟩
  · intro p hp
    have heq : beta p = (-L*p.1.2.2) • (w p • b p) := by
      simp only [beta,d,b,parameterWeightedNormalizedConformalDrift,
        parameterNormalizedConformalDrift,normalizedConformalDrift,
        parameterNormalizedConformalDriftBase,smul_smul,mul_comm,mul_left_comm,mul_assoc]
    refine ⟨?_,?_⟩
    · calc
        ‖d p‖ = |L| * |p.1.2.2| * ‖b p‖ := by
          simp only [d,b,parameterNormalizedConformalDrift,normalizedConformalDrift,
            parameterNormalizedConformalDriftBase,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
        _ ≤ |L| * |p.1.2.2| * K := mul_le_mul_of_nonneg_left (hbK p hp)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = (|L| * K)*|p.1.2.2| := by ring
        _ ≤ D*|p.1.2.2| := mul_le_mul_of_nonneg_right hLineD (abs_nonneg _)
    · change ‖beta p‖ ≤ D*|p.1.2.2|
      rw [heq]
      calc
        ‖(-L*p.1.2.2) • (w p • b p)‖ = |L| * |p.1.2.2| * ‖w p • b p‖ := by
          simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
        _ ≤ |L| * |p.1.2.2| * K := mul_le_mul_of_nonneg_left (hwK p hp)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = (|L| * K)*|p.1.2.2| := by ring
        _ ≤ D*|p.1.2.2| := mul_le_mul_of_nonneg_right hLineD (abs_nonneg _)

end OAI.AnisotropicCalderon.ConnectionError
