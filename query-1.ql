/**
 * @kind problem
 */

import go
//import DataFlow::PathGraph
import semmle.go.dataflow.TaintTracking
/*
 * 	Bad flow:
 * 	http.HandlerFunc(GetAccount) -> router.Handle
 *
 * 	OK flow:
 * 	http.HandlerFunc(GetAccount) ->  AuthorizationMiddleware() -> router.Handle()
 *
 * 	We Want to find the bad flow.
 *
 * 	If we treat AuthorizationMiddleware (the concept, not the particular function) as sanitizer,
 *  the ok flow won't show.
 */

import semmle.go.dataflow.internal.DataFlowUtil

/*
 *   Must have
 *      (profile := ) r.Header.Get("Authorization")
 *      (tokenID := ) mux.Vars(r)["id"]
 *  in one function body, along with the comparison:
 *      if (profile) != (tokenID) ...
 */

class NoAuthCheckInFunction extends FuncDef {
  NoAuthCheckInFunction() {
    not exists(CallExpr get, IndexExpr vars_id, IfStmt theIf, ComparisonExpr comp |
      //
      // r.Header.Get("Authorization")
      //
      get.getTarget().getName() = "Get" and
      get.getArgument(0).(StringLit).getValue() = "Authorization" and
      //
      // mux.Vars(r)["id"]
      //
      vars_id.getIndex().(StringLit).getValue() = "id" and
      vars_id.getBase().(CallExpr).getTarget().getName() = "Vars" and
      //
      // if _ <cmp> _
      //
      comp = theIf.getCond().(ComparisonExpr) and
      //
      // the flow DataFlow::localFlow(source, sink)
      //
      exists(DataFlow::Node source, DataFlow::Node sink |
        source.asExpr() = get and
        sink.asExpr() = comp.getAnOperand() and
        DataFlow::localFlow(source, sink)
      ) and
      exists(DataFlow::Node source, DataFlow::Node sink |
        source.asExpr() = vars_id and
        sink.asExpr() = comp.getAnOperand() and
        DataFlow::localFlow(source, sink)
      ) and
      this = theIf.getEnclosingFunction*()
    )
  }
}

class MiddlewareCall extends CallExpr {
  MiddlewareCall() {
    exists(CallExpr call, StringLit lit |
      call.getArgument(0) = lit and
      call.getArgument(1) = this and
      lit.getValue().matches("%id%") and
      call.getTarget().getName() = "Handle"
    )
  }
}

class AuthFlow extends TaintTracking::Configuration {
  AuthFlow() { this = "AuthFlow" }

  override predicate isSource(DataFlow::Node source) {
    exists(MiddlewareCall middlewarecall | middlewarecall.getArgument(0) = source.asExpr())
  }

  override predicate isSink(DataFlow::Node node) {
    // next.ServeHTTP(rw, r)
    exists(SelectorExpr sel |
      node.asExpr() = sel.getBase() and
      sel.getSelector().getName() = "ServeHTTP"
    )
  }
}

from AuthFlow auth, DataFlow::PathNode source, DataFlow::PathNode sink, CallExpr handlerCall
where
  auth.hasFlowPath(source, sink) and
  handlerCall instanceof MiddlewareCall and
  handlerCall.getTarget().getFuncDecl() instanceof NoAuthCheckInFunction
  or
  exists(StringLit lit, ConversionExpr con |
    handlerCall.getArgument(0) = lit and
    not handlerCall.getArgument(1) instanceof CallExpr and
    con.getAChildExpr().(FunctionName).getTarget().getFuncDecl() instanceof NoAuthCheckInFunction and
    lit.getValue().matches("%id%") and
    handlerCall.getTarget().getName() = "Handle"
  )
select handlerCall, handlerCall.getTarget()

