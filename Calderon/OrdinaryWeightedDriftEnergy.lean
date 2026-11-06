import Calderon.OrdinaryWeightedDriftOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

theorem unitBall_dirichletForcing_add
    (f d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (f + d) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v +
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v := by
  calc
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (f + d) v =
        ⟪f + d, TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
      TauCeti.PDE.dirichletForcing_apply (mu := (volume : Measure R3))
        (Omega := ballOpens) (f + d) v
    _ = ⟪f, TauCeti.W1p.value (v : BallH1)⟫_ℝ +
        ⟪d, TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
      inner_add_left f d (TauCeti.W1p.value (v : BallH1))
    _ = TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v +
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v :=
      congrArg₂ (fun x y : ℝ => x + y)
        (TauCeti.PDE.dirichletForcing_apply (mu := (volume : Measure R3))
          (Omega := ballOpens) f v).symm
        (TauCeti.PDE.dirichletForcing_apply (mu := (volume : Measure R3))
          (Omega := ballOpens) d v).symm

theorem ordinaryPrincipalL_energy_of_field_eq
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s + 2))
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hField : coefficientMatrixField (s + 2) F = A)
    (E : BallSobolev (s + 2)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryPrincipalL hcalc s F E)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ)
        (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (s + 1) E) (v : BallH1) := by
  have hNative := ordinaryPrincipalL_energy hcalc s F E v
  have hEnergy := congrArg (fun B : R3 → Matrix (Fin 3) (Fin 3) ℝ =>
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      B (0 : R3 → R3) (0 : R3 → ℝ)
      (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) E) (v : BallH1)) hField
  exact hNative.trans hEnergy

theorem eq_add_of_eq_of_eq_add {x y z w d : ℝ}
    (hxy : x = y) (hxz : x = z + d) (hzw : z = w) : y = w + d :=
  hxy.symm.trans (hxz.trans (congrArg (fun t : ℝ => t + d) hzw))

theorem unitBall_dirichletForcing_value_add (s : ℕ)
    (P D : BallSobolev s) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s (P + D)) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s P) v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s D) v := by
  have hValue := TauCeti.Wkp.value_add (mu := (volume : Measure R3))
    (Omega := ballOpens) (p := 2) s P D
  have hProjected := congrArg (fun f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v) hValue
  exact hProjected.trans (unitBall_dirichletForcing_add
    (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s P)
    (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s D) v)

theorem ordinaryPrincipal_add_supportedDrift_energy
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s + 2))
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (E : BallSobolev (s + 2)) (D : BallSobolev s)
    (hD : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s D =
      supportedDriftL hcalc 0 beta hbeta K hK hz
        (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (s + 1) E)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryPrincipalL hcalc s F E + D)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (s + 1) E) (v : BallH1) := by
  have hAdd := unitBall_dirichletForcing_value_add s (ordinaryPrincipalL hcalc s F E) D v
  have hPrincipal := ordinaryPrincipalL_energy hcalc s F E v
  have hDrift := congrArg (fun f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v) hD
  have hSplit := energyFormH1_eq_principal_add_driftForcing hcalc
    (coefficientMatrixField (s + 2) F) hcoeff beta hbeta K hK hz
    (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (s + 1) E) v
  exact hAdd.trans ((congrArg₂ (fun x y : ℝ => x + y) hPrincipal hDrift).trans hSplit.symm)

theorem unitBall_energyFormH1_congr_coefficient
    (A A' : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : A = A')
    (beta : R3 → R3) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A beta (0 : R3 → ℝ) u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A' beta (0 : R3 → ℝ) u (v : BallH1) :=
  congrArg (fun B : R3 → Matrix (Fin 3) (Fin 3) ℝ =>
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      B beta (0 : R3 → ℝ) u (v : BallH1)) hA

section Family
variable (hcalc : FixedSobolevCalculus) (s : ℕ)
  (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
  (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
  (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
  (K : Set R3) (hK : IsCompact K)
  (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0)
  (L : ℝ)

theorem ordinaryStrongDriftFamily_energy (p : R3 × ℝ)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) (commonSupportMatrixFamily (s + 2) a ha K hK hza p) z)
        0 0) ⊤ ((volume : Measure R3).restrict ballOpens))
    (E : BallSobolev (s + 2)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p E)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun z => a (p,z)) (weightedDriftSlice w b L p) 0
        (TauCeti.Wkp.firstOrder (s + 1) E) (v : BallH1) := by
  let F : SmoothCoefficientMatrix (s + 2) :=
    commonSupportMatrixFamily (s + 2) a ha K hK hza p
  let beta : R3 → R3 := weightedDriftSlice w b L p
  have hNative := ordinaryPrincipal_add_supportedDrift_energy hcalc s F hcoeff beta
    (contDiff_weightedDriftSlice w hw b hb L p) K hK
    (weightedDriftSlice_support w b L p K hzw) E
    (ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p E)
    (ordinaryWeightedDriftL_value_eq hcalc s w hw b hb K hK hzw L p E) v
  have hField : coefficientMatrixField (s + 2) F = fun z => a (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily (s + 2) a ha K hK hza p
  have hEnergy := unitBall_energyFormH1_congr_coefficient
    (coefficientMatrixField (s + 2) F) (fun z => a (p,z)) hField beta
    (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (s + 1) E) v
  exact hNative.trans hEnergy

end Family
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
