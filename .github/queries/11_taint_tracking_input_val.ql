/**
 * @name Taint Tracking Input Validation (La mia Query)
 * @description Rileva il flusso di dati non validato da ntohl a memcpy
 * @kind path-problem
 * @problem.severity critical
 * @id cpp/taint-tracking-custom
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking

class NetworkByteSwap extends Expr {
  NetworkByteSwap () {
    // Quantificatore esistenziale per introdurre una variabile temporanea
    exists(MacroInvocation mi |
        // Condizione: la macro deve chiamarsi ntoh, ntohs o ntohll
        mi.getMacro().getName().matches("ntoh%") and
        // Collegamento: l'espressione corrente (this) deve derivare da tale macro
        mi.getExpr() = this
    )
    }
}

module MyConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source.asExpr() instanceof NetworkByteSwap
  }
  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall fc |
      fc.getTarget().getName() = "memcpy" and
      sink.asExpr() = fc.getArgument(2)
    )
  }
  // Predicate per identificare le barriere di flusso, ad esempio chiamate a funzioni
  // che controllano se la dimensione dell'input è inferiore ad una certa soglia prima 
  // di chiamare memcpy
  predicate isBarrier(DataFlow::Node node) {
    exists(IfStmt is | 
    node.asExpr() = is.getControllingExpr().getAChild*()
  )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink) 
select sink.getNode(), source, sink, "Network byte swap flows to memcpy"

