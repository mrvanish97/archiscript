import ArchiScriptExamples.ReservationController

namespace ArchiScriptTests.ExpressionStress

open ArchiScript
open ArchiScriptExamples.ReservationController

#guard controllerExpressionFamily.expressions.length == 5
#guard controllerExpressionFamily.targets.length == 5

example :
    Expression.denote controllerPlanExpression =
      planControllerMutation := rfl

example :
    Expression.denote controllerWriteExpression =
      persistMutation.comp planControllerMutation := rfl

example :
    userPaymentFactoringCertificate.targetIso.toOperation.comp
        (Expression.denote userPaymentPlanExpression) =
      (Expression.denote userPaymentFactoredPlanExpression).comp
        userPaymentFactoringCertificate.sourceIso.toOperation :=
  userPaymentFactoringCertificate.commutes

example :
    controllerFactoringCertificate.targetIso.toOperation.comp
        (Expression.denote controllerPlanExpression) =
      (Expression.denote controllerFactoredPlanExpression).comp
        controllerFactoringCertificate.sourceIso.toOperation :=
  controllerFactoringCertificate.commutes

example :
    projectedControllerStateOperation =
      nextReservationState.comp planControllerMutation := rfl

end ArchiScriptTests.ExpressionStress
