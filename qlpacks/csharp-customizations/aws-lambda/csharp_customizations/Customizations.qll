/**
 * Contains customizations to the standard library.
 *
 * This module is imported by `csharp.qll`, so any customizations defined here automatically
 * apply to all queries.
 *
 * Typical examples of customizations include adding new subclasses of abstract classes such as
 * the `RemoteFlowSource` and `SummarizedCallable` classes associated with the security queries
 * to model frameworks that are not covered by the standard library.
 */

import csharp
private import semmle.code.csharp.frameworks.Sql
private import semmle.code.csharp.security.dataflow.flowsources.Remote
private import semmle.code.csharp.dataflow.TaintTracking5

/**
 * An AWS Lambda function handler method.
 */
class AWSLambdaFunctionHandler extends Method {
  AWSLambdaFunctionHandler() {
    // use a heuristic approach for finding Lambda function handlers with the signature
    // `public returnType handler-name(inputType input, ILambdaContext context)`
    this.getNumberOfParameters() = 2 and
    this.getParameter(1).getType().getName() = "ILambdaContext" and
    this.isPublic()
  }
}

/**
 * A model of the input parameter of each AWS Lambda function handler
 * as a source of untrusted remote data (`RemoteFlowSource`).
 */
class AWSLambdaFunctionHandlerRemoteFlowSource extends RemoteFlowSource {
  AWSLambdaFunctionHandlerRemoteFlowSource() {
    exists(AWSLambdaFunctionHandler handler |
      this.(DataFlow::ParameterNode).getParameter() = handler.getParameter(0)
    )
  }

  override string getSourceType() { result = "AWS Lambda function handler input" }
}

/**
 * This class models members, nested members, and templated nested members
 * of AWS Lambda function handler input types. It extends the `TaintTracking::TaintedMember`
 * class in order to add additional edges between the input variable and its members.
 */
private class FunctionHandlerInputMember extends TaintTracking::TaintedMember {
  FunctionHandlerInputMember() {
    exists(AWSLambdaFunctionHandler handler, Class c |
      handler.getParameter(0).getType() = c and
      (
        this.getDeclaringType() = c or
        this.getDeclaringType() = c.getAMember*().(Property).getType() or
        this.getDeclaringType() =
          c.getAMember*().(Property).getType().(ConstructedGeneric).getATypeArgument()
      )
    )
  }
}

/**
 * An assignment to the `*StatementRequest.Statement` properties.
 */
class AmazonDynamoDBStatementRequestStatementAssignment extends AssignExpr {
  AmazonDynamoDBStatementRequestStatementAssignment() {
    this.getLValue()
        .(PropertyAccess)
        .getTarget()
        .hasQualifiedName([
            "Amazon.DynamoDBv2.Model.ExecuteStatementRequest.Statement",
            "Amazon.DynamoDBv2.Model.BatchStatementRequest.Statement",
          ])
  }
}

/**
 * A flow configuration for tracking taint flow from query statement assignment to execution.
 */
private class StatementToExecuteStatementAsyncConf extends TaintTracking5::Configuration {
  StatementToExecuteStatementAsyncConf() { this = "ExecuteStatementAsyncSqlFlowConfig" }

  override predicate isSource(DataFlow::Node src) {
    exists(AmazonDynamoDBStatementRequestStatementAssignment expr | src.asExpr() = expr.getRValue())
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(MethodCall mc |
      mc.getTarget()
          .hasQualifiedName("Amazon.DynamoDBv2.IAmazonDynamoDB",
            [
              "ExecuteStatement", "ExecuteStatementAsync", "BatchExecuteStatement",
              "BatchExecuteStatementAsync"
            ]) and
      sink.asExpr() = mc.getArgument(0)
    )
  }

  override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    node1.getType() instanceof StringType and
    exists(PropertyWrite pw, Property p, Assignment a |
      a.getLValue() = pw and
      pw.getProperty() = p and
      p.getDeclaringType()
          .hasQualifiedName("Amazon.DynamoDBv2.Model",
            ["ExecuteStatementRequest", "BatchStatementRequest"]) and
      p.hasName("Statement") and
      (
        node1.asExpr() = a.getRValue() and
        node2.asExpr() = pw.getQualifier()
        or
        exists(ObjectInitializer oi |
          node1.asExpr() = oi.getAMemberInitializer().getRValue() and
          node2.asExpr() = oi
        )
      )
    )
  }
}

/**
 * An expression representing the query string assigned to a statement which flows
 * to the argument of an `ExecuteStatement*` method call.
 */
class AmazonDynamoDBExecuteStatementRequestSqlExpr extends SqlExpr,
  AmazonDynamoDBStatementRequestStatementAssignment {
  AmazonDynamoDBExecuteStatementRequestSqlExpr() {
    exists(StatementToExecuteStatementAsyncConf conf |
      conf.hasFlow(DataFlow::exprNode(this.getRValue()), _)
    )
  }

  override Expr getSql() { result = this.getRValue() }
}
