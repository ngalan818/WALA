package com.ibm.wala.cast.ir.translator;

import com.ibm.wala.cast.tree.CAstEntity;
import com.ibm.wala.cast.tree.impl.CAstImpl;
import com.ibm.wala.cast.tree.rewrite.CAstRewriter.CopyKey;
import com.ibm.wala.cast.tree.rewrite.CAstRewriter.RewriteContext;
import com.ibm.wala.cast.tree.rewrite.CAstRewriterFactory;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class RewritingTranslatorToCAst implements TranslatorToCAst {
  private final List<CAstRewriterFactory<?, ?>> rewriters = new LinkedList<>();
  private final TranslatorToCAst base;

  public RewritingTranslatorToCAst(TranslatorToCAst base) {
    this.base = base;
  }

  @Override
  public <C extends RewriteContext<K>, K extends CopyKey<K>> void addRewriter(
      CAstRewriterFactory<C, K> factory, boolean prepend) {
    if (prepend) rewriters.add(0, factory);
    else rewriters.add(factory);
  }

  @Override
  public CAstEntity translateToCAst() throws IOException, Error {
    CAstImpl Ast = new CAstImpl();
    CAstEntity entity = base.translateToCAst();
    for (CAstRewriterFactory<?, ?> rwf : rewriters)
      entity = rwf.createCAstRewriter(Ast).rewrite(entity);
    return entity;
  }
}
