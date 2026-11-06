import Calderon.CoordinateFluxEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-! Exact native principal-plus-drift L2 flux bridge, arbitrary coefficient
fields/rough H1 inputs; full interface expanded and sealed before body.
No actual flow/hData, desired energy or smoothness premise is captured. -/

theorem energyFormH1_eq_sum_coordinateFlux_inner_add_drift
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (b : R3 → R3) (u v : BallH1)
    (Q : Fin 3 → Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hQ : ∀ i j : Fin 3, Q i j =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => a x i j * (TauCeti.W1p.gradient u x) j)
    (hR : ∀ i : Fin 3, R i =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => b x i * (TauCeti.W1p.gradient u x) i) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b 0 u v =
      (∑ i : Fin 3, ∑ j : Fin 3, ⟪Q i j, unitBallCoordinateGradientL i v⟫_ℝ) +
        ∑ i : Fin 3, ⟪R i, TauCeti.W1p.value v⟫_ℝ := by
  let z : Fin 3 → Fin 3 → R3 → ℝ := fun i j x =>
    ⟪Q i j x,unitBallCoordinateGradientL i v x⟫_ℝ
  let zR : Fin 3 → R3 → ℝ := fun i x => ⟪R i x,TauCeti.W1p.value v x⟫_ℝ
  have hi (i j : Fin 3) : Integrable (z i j)
      ((volume : Measure R3).restrict ballOpens) :=
    L2.integrable_inner (𝕜 := ℝ) (Q i j) (unitBallCoordinateGradientL i v)
  have hiR (i : Fin 3) : Integrable (zR i)
      ((volume : Measure R3).restrict ballOpens) :=
    L2.integrable_inner (𝕜 := ℝ) (R i) (TauCeti.W1p.value v)
  have hf : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i j : Fin 3,
      Q i j x = a x i j * (TauCeti.W1p.gradient u x) j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hQ i j
  have hr : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      R i x = b x i *
        (TauCeti.W1p.gradient u x) i := ae_all_iff.mpr fun i => hR i
  have hg : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      unitBallCoordinateGradientL i v x = (TauCeti.W1p.gradient v x) i :=
    ae_all_iff.mpr fun i => unitBallCoordinateGradientL_ae i v
  have hSumP : (∫ x in ballOpens, ∑ i : Fin 3, ∑ j : Fin 3, z i j x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in ballOpens, z i j x := by
    calc
      _ = ∑ i : Fin 3, ∫ x in ballOpens, ∑ j : Fin 3, z i j x :=
        integral_finsetSum (μ := (volume : Measure R3).restrict ballOpens)
          (f := fun i x => ∑ j : Fin 3, z i j x) Finset.univ
          (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum (μ := (volume : Measure R3).restrict ballOpens)
          (f := fun j x => z i j x) Finset.univ (fun j _ => hi i j)
  have hSumR : (∫ x in ballOpens, ∑ i : Fin 3, zR i x) =
      ∑ i : Fin 3, ∫ x in ballOpens, zR i x :=
    integral_finsetSum (μ := (volume : Measure R3).restrict ballOpens)
      (f := fun i x => zR i x) Finset.univ (fun i _ => hiR i)
  calc
    _ = ∫ x in ballOpens, (∑ i, ∑ j, z i j x) + ∑ i, zR i x := by
      rw [TauCeti.PDE.energyFormH1_def]
      apply integral_congr_ae
      filter_upwards [hf,hr,hg] with x hx hxr hxg
      simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,
        TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,Pi.zero_apply,
        zero_mul,add_zero,TauCeti.PDE.matrixBilinearForm_apply,Matrix.mulVec,dotProduct,
        Finset.mul_sum,EuclideanSpace.inner_eq_star_dotProduct,Pi.star_apply,star_trivial,
        Finset.sum_mul]
      apply congrArg₂ (fun x y : ℝ => x+y)
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [z,RCLike.inner_apply,conj_trivial]
        rw [hx i j,hxg i]
      · apply Finset.sum_congr rfl
        intro i _
        simp only [zR,RCLike.inner_apply,conj_trivial]
        rw [hxr i]
        ring
    _ = _ := by
      rw [integral_add
        (integrable_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hi i j)))
        (integrable_finsetSum Finset.univ (fun i _ => hiR i))]
      rw [hSumP,hSumR]
      simp only [L2.inner_def,z,zR]

end OAI.AnisotropicCalderon.DirichletFamily
