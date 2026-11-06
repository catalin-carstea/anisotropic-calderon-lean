import Calderon.ActualReferenceRadialRotationCommutatorMidpointCasimirBlock
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection

/-! Full upfront: EXPANSION-v005.json. Original physical actual Casimir pairing,
via a fixed actual harmonic scalar functional and finite value-level map identities. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma referenceRadialRotationCommutatorMidpoint_harmonic_casimir_form
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (m n : ℕ) (u : harmonicSphereSubspace n) (v : harmonicSphereSubspace m) :
    ((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) *
      ⟪referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 p m n u,v⟫_ℝ =
    (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3,(
      ⟪referenceRadialRotationCommutatorMidpointHarmonicBlockL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p m n u,
        harmonicSphereRotation m i j v⟫_ℝ -
      ⟪referenceRadialRotationCommutatorMidpointHarmonicBlockL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p m n
          (harmonicSphereRotation n i j u),v⟫_ℝ)) := by
  let K : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
    referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p m n
  let D (i j : Fin 3) : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
    referenceRadialRotationCommutatorMidpointHarmonicBlockL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p m n
  let c : ℝ := (m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)
  let ℓ : harmonicSphereSubspace m →L[ℝ] ℝ := innerSL ℝ v
  let T (i j : Fin 3) : harmonicSphereSubspace m :=
    harmonicSphereRotation m i j (D i j u) + D i j (harmonicSphereRotation n i j u)
  let S (i j : Fin 3) : ℝ :=
    ⟪D i j u,harmonicSphereRotation m i j v⟫_ℝ -
      ⟪D i j (harmonicSphereRotation n i j u),v⟫_ℝ
  have hEval (x : harmonicSphereSubspace m) : ℓ x = ⟪x,v⟫_ℝ := by
    change ⟪v,x⟫_ℝ = ⟪x,v⟫_ℝ
    exact real_inner_comm x v
  have hVector : c • K u = (-(1/2:ℝ)) • (∑ i : Fin 3, ∑ j : Fin 3, T i j) :=
    referenceRadialRotationCommutatorMidpoint_harmonic_casimir_block
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp m n u
  have hTerm (i j : Fin 3) : ℓ (T i j) = -(S i j) := by
    have hFirst : ℓ (harmonicSphereRotation m i j (D i j u)) =
        -⟪D i j u,harmonicSphereRotation m i j v⟫_ℝ :=
      (hEval (harmonicSphereRotation m i j (D i j u))).trans
        (inner_harmonicSphereRotation_skew m i j (D i j u) v)
    calc
      _ = ℓ (harmonicSphereRotation m i j (D i j u)) +
          ℓ (D i j (harmonicSphereRotation n i j u)) := ℓ.map_add _ _
      _ = -⟪D i j u,harmonicSphereRotation m i j v⟫_ℝ +
          ⟪D i j (harmonicSphereRotation n i j u),v⟫_ℝ :=
        congrArg₂ (fun x y : ℝ => x+y) hFirst (hEval (D i j (harmonicSphereRotation n i j u)))
      _ = _ := by change _ = -(⟪D i j u,harmonicSphereRotation m i j v⟫_ℝ -
          ⟪D i j (harmonicSphereRotation n i j u),v⟫_ℝ); ring
  have hMapSum : ℓ (∑ i : Fin 3, ∑ j : Fin 3, T i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, ℓ (T i j) := by
    calc
      _ = ∑ i : Fin 3, ℓ (∑ j : Fin 3, T i j) :=
        map_sum ℓ (fun i : Fin 3 => ∑ j : Fin 3, T i j) Finset.univ
      _ = _ := Finset.sum_congr rfl (fun i _ => map_sum ℓ (T i) Finset.univ)
  have hPairSum : (∑ i : Fin 3, ∑ j : Fin 3, ℓ (T i j)) =
      -(∑ i : Fin 3, ∑ j : Fin 3, S i j) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, -(S i j) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hTerm i j))
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hLeft : ℓ (c • K u) = c * ⟪K u,v⟫_ℝ :=
    (ℓ.map_smul c (K u)).trans (congrArg (fun z : ℝ => c*z) (hEval (K u)))
  have hRight : ℓ ((-(1/2:ℝ)) • (∑ i : Fin 3, ∑ j : Fin 3, T i j)) =
      (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, S i j) := by
    calc
      _ = (-(1/2:ℝ)) * ℓ (∑ i : Fin 3, ∑ j : Fin 3, T i j) := ℓ.map_smul _ _
      _ = (-(1/2:ℝ)) * -(∑ i : Fin 3, ∑ j : Fin 3, S i j) :=
        congrArg (fun z : ℝ => (-(1/2:ℝ))*z) (hMapSum.trans hPairSum)
      _ = _ := by ring
  exact hLeft.symm.trans ((congrArg (fun x : harmonicSphereSubspace m => ℓ x) hVector).trans hRight)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpoint_harmonic_casimir_form
