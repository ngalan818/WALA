/*
 * Copyright (c) 2002 - 2024 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 */
package com.ibm.wala.cast.test;

import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.net.MalformedURLException;
import java.net.URL;

import org.junit.Assert;
import org.junit.Test;

import com.ibm.wala.cast.tree.CAstSourcePositionMap.Position;
import com.ibm.wala.cast.util.SourceBuffer;
import com.ibm.wala.classLoader.IMethod.SourcePosition;

public class TestSourceBuffer {
  final static String INDENT = "           "; // whitespaces in column 1:11

  private URL getSourceUrl() throws MalformedURLException {
    File testSourceBufferCbl = 
      new File(getClass().getClassLoader().getResource("test_sourcebuffer.cbl").getFile());
    return new URL("file:" + testSourceBufferCbl.getAbsolutePath());
  }

  private Position mockPosition(final int firstLine, final int firstCol, final int lastLine,
    final int lastCol, final int firstOffset, final int lastOffset) throws MalformedURLException {
    URL src = getSourceUrl();
    
    Position position = new Position() {

			@Override
			public int getFirstLine() {
				return firstLine;
			}

			@Override
			public int getLastLine() {
				return lastLine;
			}

			@Override
			public int getFirstCol() {
				return firstCol - 1;  // 0-base indexing
			}

			@Override
			public int getLastCol() {
				return lastCol - 1; // 0-base
			}

			@Override
			public int getFirstOffset() {
        return firstOffset;
			}

			@Override
			public int getLastOffset() {
        return lastOffset;
			}

			@Override
			public int compareTo(SourcePosition o) {
				return -1;
			}

			@Override
			public URL getURL() {
				return src;
			}

			@Override
			public Reader getReader() throws IOException {
				return new InputStreamReader(src.openStream());
			}
    };

    System.err.println("position: " + position);
    return position;
  }

  private static void testEqualString(final String actual, final String expected) {
    Assert.assertTrue("expected '" + expected + "' but got '" + actual + "'", actual.equals(expected));
  }

  @Test
  public void testSingleLineNoOffset() throws IOException {
    // position of "ACCEPT WS-INPUT." [2:12] -> [2:27] (1-base indexing)
    Position position = mockPosition(2, 12, 2, 27, -1, -1);
      
    String sourceBufferString = new SourceBuffer(position).toString();
    testEqualString(sourceBufferString, "ACCEPT WS-INPUT.");
  }

  @Test
  public void testMultiLineNoOffset() throws IOException {
    /* position of "
        IF WS-INPUT = 0
        GO TO IS-ZERO
        ELSE
        GO TO END-PROGRAM." [3:12] -> [6:29] (1-base indexing)
     */
    Position position = mockPosition(3, 12, 6, 29, -1, -1);
      
    String sourceBufferString = new SourceBuffer(position).toString();
    testEqualString(sourceBufferString, "IF WS-INPUT = 0\n" + 
      INDENT + "GO TO IS-ZERO\n" + 
      INDENT + "ELSE\n" + 
      INDENT + "GO TO END-PROGRAM.");
    
  }

}
