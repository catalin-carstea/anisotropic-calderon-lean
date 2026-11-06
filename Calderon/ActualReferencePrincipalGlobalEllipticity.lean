import Calderon.ActualJointReferenceCoefficientData
import Calderon.WeightedCommonSupportCoefficients

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

lemma exists_referencePrincipal_uniformlyElliptic_closedBall_on_compact
    (q : Set (ℝ × (R3 × ℝ))) (hq : IsCompact q) :
    ∃ lam Lam : ℝ, ∀ p ∈ q,
      TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
        (fun x => a (p,x)) lam Lam := by
  have ha : a = cutoffPrincipalCoefficient H := hData.1.2.2.2.2.1
  have hH : ContDiff ℝ ∞ H := hData.1.2.2.2.2.2.2.1
  have hpos : ∀ p, (H p).PosDef := hData.1.2.2.2.2.2.2.2.1
  simpa only [ha] using exists_uniformlyElliptic_cutoffPrincipalCoefficient H hH hpos q hq

lemma exists_referencePrincipal_uniformlyElliptic_on_compact
    (q : Set (ℝ × (R3 × ℝ))) (hq : IsCompact q) :
    ∃ lam Lam : ℝ, ∀ p ∈ q,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun x => a (p,x)) lam Lam := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic_closedBall_on_compact
    g L y0 Φ B ε C ρ H a w hData q hq
  refine ⟨lam,Lam,?_⟩
  intro p hp
  refine ⟨(hUE p hp).1,(hUE p hp).2.1,?_⟩
  intro x hx
  exact (hUE p hp).2.2 (by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hx)

lemma exists_referencePrincipal_uniformlyElliptic
    (p : ℝ × (R3 × ℝ)) :
    ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun x => a (p,x)) lam Lam := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic_on_compact
    g L y0 Φ B ε C ρ H a w hData {p} isCompact_singleton
  exact ⟨lam,Lam,hUE p (mem_singleton p)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePrincipal_uniformlyElliptic_closedBall_on_compact

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePrincipal_uniformlyElliptic_on_compact

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePrincipal_uniformlyElliptic
