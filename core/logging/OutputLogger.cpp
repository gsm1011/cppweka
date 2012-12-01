/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 * OutputLogger.cpp
 * Copyright (C) 2008 University of Waikato, Hamilton, New Zealand
 */

// package weka.core.logging;

// import weka.core.RevisionUtils;
// import weka.core.Tee;

// import java.io.PrintStream;
// import java.util.Date;

/**
 * A logger that logs all output on stdout and stderr to a file.
 * 
 * @author  fracpete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 4716 $
 */
class OutputLogger : public FileLogger {
public:
  /**
   * A print stream class to capture all data from stdout and stderr.
   * 
   * @author  fracpete (fracpete at waikato dot ac dot nz)
   * @version $Revision: 4716 $
   */
  static class OutputPrintStream : public PrintStream {
  protected: 
    /** the owning logger. */
    OutputLogger m_Owner;
    
    /** the line feed. */
    string m_LineFeed;
    
  public:
    /**
     * Default constructor.
     * 
     * @param owner		the owning logger
     * @param stream		the stream
     * @throws Exception	if something goes wrong
     */
    OutputPrintStream(OutputLogger owner, PrintStream stream) :
      * FileLogger(stream), m_Owner(owner) throws Exception {
      // super(stream);
      
      // m_Owner    = owner;
      m_LineFeed = System.getProperty("line.separator");
    }

    /**
     * ignored.
     */
    void flush() {
    }

    /**
     * prints the given int to the streams.
     * 
     * @param x 	the object to print
     */
    void print(int x) {
      m_Owner.append("" + x);
    }

    /**
     * prints the given bool to the streams.
     * 
     * @param x 	the object to print
     */
    void print(bool x) {
      m_Owner.append("" + x);
    }

    /**
     * prints the given string to the streams.
     * 
     * @param x 	the object to print
     */
    void print(string x) {
      m_Owner.append("" + x);
    }

    /**
     * prints the given object to the streams.
     * 
     * @param x 	the object to print
     */
    void print(Object x) {
      m_Owner.append("" + x);
    }

    /**
     * prints a new line to the streams.
     */
    void println() {
      m_Owner.append(m_LineFeed);
    }

    /**
     * prints the given int to the streams.
     * 
     * @param x 	the object to print
     */
    void println(int x) {
      m_Owner.append(x + m_LineFeed);
    }

    /**
     * prints the given bool to the streams.
     * 
     * @param x 	the object to print
     */
    void println(bool x) {
      m_Owner.append(x + m_LineFeed);
    }

    /**
     * prints the given string to the streams.
     * 
     * @param x 	the object to print
     */
    void println(string x) {
      m_Owner.append(x + m_LineFeed);
    }

    /**
     * prints the given object to the streams (for Throwables we print the stack
     * trace).
     * 
     * @param x 	the object to print
     */
    void println(Object x) {
      m_Owner.append(x + m_LineFeed);
    }
  }
  
protected:
  /** the stream object used for logging stdout. */
  OutputPrintStream m_StreamOut;
  
  /** the stream object used for logging stderr. */
  OutputPrintStream m_StreamErr;

  /** the Tee instance to redirect stdout. */
  Tee m_StdOut;

  /** the Tee instance to redirect stderr. */
  Tee m_StdErr;
  
  /**
   * Initializes the logger.
   */
  void initialize() {
    super.initialize();
    
    try {
      m_StdOut = new Tee(System.out);
      System.setOut(m_StdOut);
      m_StreamOut = new OutputPrintStream(this, m_StdOut.getDefault());
      m_StdOut.add(m_StreamOut);
      
      m_StdErr = new Tee(System.err);
      System.setErr(m_StdErr);
      m_StreamErr = new OutputPrintStream(this, m_StdErr.getDefault());
      m_StdErr.add(m_StreamErr);
    }
    catch (Exception e) {
      // ignored
    }
  }
  
  /**
   * Performs the actual logging. 
   * 
   * @param level	the level of the message
   * @param msg		the message to log
   * @param cls		the classname originating the log event
   * @param method	the method originating the log event
   * @param lineno	the line number originating the log event
   */
  void doLog(Level level, string msg, string cls, string method, int lineno) {
    // append output to file
    append(
	m_DateFormat.format(new Date()) + " " + cls + " " + method + m_LineFeed
	+ level + ": " + msg + m_LineFeed);
  }
  
public:
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 4716 $");
  }
};
