package com.ibm.wala.ssa;

public class SSAUnspecifiedInstruction<T> extends SSAInstruction {
  private final T payload;

  public SSAUnspecifiedInstruction(int iindex, T payload) {
    super(iindex);
    this.payload = payload;
  }

  @Override
  public SSAInstruction copyForSSA(SSAInstructionFactory insts, int[] defs, int[] uses) {
    return this;
  }

  @Override
  public String toString(SymbolTable symbolTable) {
    return payload.toString();
  }

  @Override
  public void visit(IVisitor v) {
    v.visitUnspecified(this);
  }

  @Override
  public int hashCode() {
    return payload.hashCode();
  }

  public T getPayload() {
    return payload;
  }

  @Override
  public boolean isFallThrough() {
    return true;
  }
}
