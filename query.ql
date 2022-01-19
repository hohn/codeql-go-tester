/**
 * @kind problem
 */

import go
import semmle.go.dataflow.TaintTracking
/*
 * 	Bad flow:
 * 	http.HandlerFunc(GetAccount) -> router.Handle
 *
 *  Bad flow:
 *  http.HandlerFunc(GetAccount) -> No auth check in AuthorizationMiddleware() -> router.Handle()
 *
 * 	OK flow:
 * 	http.HandlerFunc(GetAccount) ->  AuthorizationMiddleware() -> router.Handle()
 *
 * 	We Want to find the bad flow.
 */

import semmle.go.dataflow.internal.DataFlowUtil

/*
 *   Must have
 *      (profile := ) r.Header.Get("Authorization")
 *      (tokenID := ) mux.Vars(r)["id"]
 *  in one function body, along with the comparison:
 *      if (profile) != (tokenID) ...
 */

class AuthValidator extends FuncDecl {
  AuthValidator() {
    exists(CallExpr get, IndexExpr vars_id, IfStmt theIf, ComparisonExpr comp |
      //
      // r.Header.Get("Authorization")
      //
      get.getTarget().getName() = "Get" and
      get.getArgument(0).(StringLit).getValue() = "Authorization" and
      //
      // mux.Vars(r)["id"]
      //
      vars_id.getIndex().(StringLit).getValue().matches("%id%") and
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

/*
 *   The `next` part of `next.ServeHTTP(rw, r)` (may be absent, see flow.)
 */

class ServeCall extends Expr {
  ServeCall() {
    exists(SelectorExpr sel |
      sel.getBase() = this and
      sel.getSelector().getName() = "ServeHTTP"
    )
  }
}

/*
 * Identify type HandlerFunc func(ResponseWriter, *Request)
 */

predicate isHandlerFunc(FunctionName fn) {
  fn.getTarget().getParameterType(0).getName() = "ResponseWriter" and
  fn.getTarget().getParameterType(1).(PointerType).getBaseType().getName() = "Request"
}

// A route handler function like
//     router.Handle("/account/{id}", AuthorizationMiddleware(http.HandlerFunc(GetAccount)))
// Signature must be  type HandlerFunc func(ResponseWriter, *Request)
predicate isArgToCall(FunctionName fn) {
  exists(CallExpr handle, StringLit lit |
    handle.getArgument(1).getAChild*() = fn and
    handle.getArgument(0) = lit and
    //This can be improved to check for value in between the {} and pass that to the AuthValidator
    lit.getValue().matches("%id%")
  )
}

class AuthFlow extends TaintTracking::Configuration {
  AuthFlow() { this = "AuthFlow" }

  override predicate isSource(DataFlow::Node source) {
    exists(FunctionName handler |
      isArgToCall(handler) and
      isHandlerFunc(handler) and
      source.asExpr() = handler
    )
  }

  override predicate isSink(DataFlow::Node node) {
    node.asExpr() instanceof ServeCall and
    exists(FuncDecl fn | node.asExpr().getEnclosingFunction*() = fn and fn instanceof AuthValidator)
  }
}

from FunctionName anySource
where
  isArgToCall(anySource) and
  isHandlerFunc(anySource) and
  not exists(AuthFlow auth, DataFlow::Node source, DataFlow::Node sink |
    source.asExpr() = anySource and
    auth.hasFlow(source, sink)
  )
select anySource, "This handler is not wrapped by an authorization checker"
