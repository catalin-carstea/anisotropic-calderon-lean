import Calderon.ActualReferenceRadialRotationCommutatorMidpointCasimirForm
import Calderon.SphereSobolevFinitePhysicalPairing

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection

/-! Actual unbalanced finite probability-L2 Casimir identity. Cmid outputs remain unrestricted; actual Csharp is not assumed. -/
attribute [local irreducible] referenceRadialRotationCommutatorMidpointFamily
  referenceSharpRadialHarmonicBlockL referenceRadialRotationCommutatorMidpointHarmonicBlockL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma referenceRadialRotationCommutatorMidpoint_finite_physical_casimir_form
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (s t : Finset ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    (∑ m ∈ t, ∑ n ∈ s,
      (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) *
        ⟪referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 p m n (u n),v m⟫_ℝ)) =
    (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, (
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (referenceRadialRotationCommutatorMidpointFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
            (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))),
        (∑ m ∈ t, (harmonicSphereRotation m i j (v m) : SphereL2))⟫_ℝ -
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (referenceRadialRotationCommutatorMidpointFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
            (∑ n ∈ s, sphereSobolevSingleL 1 n (harmonicSphereRotation n i j (u n)))),
        (∑ m ∈ t, (v m : SphereL2))⟫_ℝ)) := by
  let Cop (i j : Fin 3) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    referenceRadialRotationCommutatorMidpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
  let Dop (i j : Fin 3) (m n : ℕ) : harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
    referenceRadialRotationCommutatorMidpointHarmonicBlockL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p m n
  let Term (m n : ℕ) (i j : Fin 3) : ℝ :=
    ⟪Dop i j m n (u n),harmonicSphereRotation m i j (v m)⟫_ℝ -
      ⟪Dop i j m n (harmonicSphereRotation n i j (u n)),v m⟫_ℝ
  let First (i j : Fin 3) : ℝ :=
    ⟪(sphereSobolevZeroEquiv hO hD).symm (Cop i j (∑ n ∈ s, sphereSobolevSingleL 1 n (u n))),
      (∑ m ∈ t, (harmonicSphereRotation m i j (v m) : SphereL2))⟫_ℝ
  let Second (i j : Fin 3) : ℝ :=
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (Cop i j (∑ n ∈ s, sphereSobolevSingleL 1 n (harmonicSphereRotation n i j (u n)))),
      (∑ m ∈ t, (v m : SphereL2))⟫_ℝ
  have hPoint (m n : ℕ) :
      (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) *
        ⟪referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 p m n (u n),v m⟫_ℝ) =
      (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, Term m n i j) :=
    referenceRadialRotationCommutatorMidpoint_harmonic_casimir_form
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp m n (u n) (v m)
  have hFirst (i j : Fin 3) : First i j =
      ∑ m ∈ t, ∑ n ∈ s, ⟪Dop i j m n (u n),harmonicSphereRotation m i j (v m)⟫_ℝ := by
    simpa only [First, Cop, Dop, referenceRadialRotationCommutatorMidpointHarmonicBlockL,
      ContinuousLinearMap.comp_apply] using
      inner_zeroEquiv_symm_clm_finite_packets hO hD (Cop i j) s t u
        (fun m => harmonicSphereRotation m i j (v m))
  have hSecond (i j : Fin 3) : Second i j =
      ∑ m ∈ t, ∑ n ∈ s, ⟪Dop i j m n (harmonicSphereRotation n i j (u n)),v m⟫_ℝ := by
    simpa only [Second, Cop, Dop, referenceRadialRotationCommutatorMidpointHarmonicBlockL,
      ContinuousLinearMap.comp_apply] using
      inner_zeroEquiv_symm_clm_finite_packets hO hD (Cop i j) s t
        (fun n => harmonicSphereRotation n i j (u n)) v
  have hExchange : (∑ m ∈ t, ∑ n ∈ s, ∑ i : Fin 3, ∑ j : Fin 3, Term m n i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ m ∈ t, ∑ n ∈ s, Term m n i j := by
    calc
      _ = ∑ m ∈ t, ∑ i : Fin 3, ∑ n ∈ s, ∑ j : Fin 3, Term m n i j :=
        Finset.sum_congr rfl (fun m _ => Finset.sum_comm)
      _ = ∑ i : Fin 3, ∑ m ∈ t, ∑ n ∈ s, ∑ j : Fin 3, Term m n i j := Finset.sum_comm
      _ = ∑ i : Fin 3, ∑ m ∈ t, ∑ j : Fin 3, ∑ n ∈ s, Term m n i j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun m _ => Finset.sum_comm))
      _ = _ := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have hPair (i j : Fin 3) : (∑ m ∈ t, ∑ n ∈ s, Term m n i j) = First i j - Second i j := by
    calc
      _ = (∑ m ∈ t, ∑ n ∈ s,
            ⟪Dop i j m n (u n),harmonicSphereRotation m i j (v m)⟫_ℝ) -
          ∑ m ∈ t, ∑ n ∈ s,
            ⟪Dop i j m n (harmonicSphereRotation n i j (u n)),v m⟫_ℝ := by
        simp only [Term, Finset.sum_sub_distrib]
      _ = _ := congrArg₂ (fun x y : ℝ => x-y) (hFirst i j).symm (hSecond i j).symm
  calc
    _ = ∑ m ∈ t, ∑ n ∈ s, (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, Term m n i j) :=
      Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hPoint m n))
    _ = (1/2:ℝ) * (∑ m ∈ t, ∑ n ∈ s, ∑ i : Fin 3, ∑ j : Fin 3, Term m n i j) := by
      simp only [Finset.mul_sum]
    _ = (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, ∑ m ∈ t, ∑ n ∈ s, Term m n i j) :=
      congrArg (fun z : ℝ => (1/2:ℝ)*z) hExchange
    _ = (1/2:ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, (First i j - Second i j)) :=
      congrArg (fun z : ℝ => (1/2:ℝ)*z)
        (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hPair i j)))
    _ = _ := rfl

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpoint_finite_physical_casimir_form

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
