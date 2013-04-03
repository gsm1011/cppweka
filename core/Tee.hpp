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

#include <time.h>
#include <iostream> 
#include <vector>

using namespace std; 

/**
* This class pipelines print/println's to several PrintStreams. Useful for
* redirecting System.out and System.err to files etc.<br/>
* E.g., for redirecting stderr/stdout to files with timestamps and:<br/>
* <pre>
*    import java.io.*;
*    import weka.core.Tee;
*
*    ...
*    // stdout
*    Tee teeOut = new Tee(System.out);
*    teeOut.add(new PrintStream(new FileOutputStream("out.txt")), true);
*    System.setOut(teeOut);
*    
*    // stderr
*    Tee teeErr = new Tee(System.err);
*    teeErr.add(new PrintStream(new FileOutputStream("err.txt")), true);
*    System.setOut(teeErr);
*    ...
* </pre>
*
* @author   FracPete (fracpete at waikato dot ac dot nz)
* @version  $Revision: 5057 $
*/

class Tee : public PrintStream, public RevisionHandler {
  
  /** the different PrintStreams. */
protected:
  Vector m_Streams;
  
  /** whether to add timestamps or not. */
  Vector m_Timestamps;
  
  /** whether to add a prefix or not. */
  Vector m_Prefixes;
  
  /** the default printstream. */
  PrintStream m_Default;

public:
  /**
   * initializes the object, with a default printstream.
   */
  Tee() {
      m_Streams = new Vector();
      m_Timestamps = new Vector();
      m_Prefixes = new Vector();
      m_Default = NULL;

      this(NULL);
  }

  /**
   * initializes the object with the given default printstream, e.g.,
   * System.out.
   * 
   * @param def     the default printstream, remains also after calling clear()
   */
  Tee(PrintStream def) {
    super(def);
    m_Streams = new Vector();
    m_Timestamps = new Vector();
    m_Prefixes = new Vector();

    m_Default = def;
    clear();
  }

  /**
   * removes all streams and places the default printstream, if any, again in
   * the list.
   * 
   * @see #getDefault()
   */
  void clear() {
    m_Streams.clear();
    m_Timestamps.clear();
    m_Prefixes.clear();
    
    if (getDefault() != NULL)
      add(getDefault());
  }

  /**
   * returns the default printstrean, can be NULL.
   * 
   * @return the default printstream
   * @see #m_Default
   */
  PrintStream getDefault() {
    return m_Default;
  }

  /**
   * adds the given PrintStream to the list of streams, with NO timestamp and
   * NO prefix.
   * 
   * @param p       the printstream to add
   */
    void add(PrintStream p);

  /**
   * adds the given PrintStream to the list of streams, with NO prefix.
   * 
   * @param p           the printstream to add
   * @param timestamp   whether to use timestamps or not
   */
    void add(PrintStream p, bool timestamp);

  /**
   * adds the given PrintStream to the list of streams.
   * 
   * @param p           the printstream to add
   * @param timestamp   whether to use timestamps or not
   * @param prefix      the prefix to use
   */
    void add(PrintStream p, bool timestamp, string prefix); 

  /**
   * returns the specified PrintStream from the list.
   * 
   * @param index the index of the PrintStream to return
   * @return the specified PrintStream, or NULL if invalid index
   */
    PrintStream get(int index);

  /**
   * removes the given PrintStream from the list.
   * 
   * @param p the PrintStream to remove
   * @return returns the removed PrintStream if it could be removed, NULL otherwise
   */
    PrintStream remove(PrintStream p);

  /**
   * removes the given PrintStream from the list.
   * 
   * @param index the index of the PrintStream to remove
   * @return returns the removed PrintStream if it could be removed, NULL otherwise
   */
    PrintStream remove(int index);

  /**
   * checks whether the given PrintStream is already in the list.
   * 
   * @param p the PrintStream to look for
   * @return true if the PrintStream is in the list
   */
    bool contains(PrintStream p);

  /**
   * returns the number of streams currently in the list.
   * 
   * @return the number of streams in the list
   */
    int size() {
	return m_Streams.size();
    }

  /**
   * prints the prefix/timestamp (timestampe only to those streams that want
   * one).
   */
private: 
    void printHeader();

  /**
   * flushes all the printstreams.
   */
    void flush();

  /**
   * prints the given int to the streams.
   * 
   * @param x the object to print
   */
    void print(int x);

  /**
   * prints the given long to the streams.
   * 
   * @param x the object to print
   */
    void print(long x);

  /**
   * prints the given float to the streams.
   * 
   * @param x the object to print
   */
    void print(float x);

  /**
   * prints the given double to the streams.
   * 
   * @param x the object to print
   */
    void print(double x);

  /**
   * prints the given bool to the streams.
   * 
   * @param x the object to print
   */
    void print(bool x);

  /**
   * prints the given char to the streams.
   * 
   * @param x the object to print
   */
    void print(char x);

  /**
   * prints the given char array to the streams.
   * 
   * @param x the object to print
   */
    void print(char[] x);

  /**
   * prints the given string to the streams.
   * 
   * @param x the object to print
   */
    void print(string x);

  /**
   * prints the given object to the streams.
   * 
   * @param x the object to print
   */
    void print(Object x);

  /**
   * prints a new line to the streams.
   */
    void println();

  /**
   * prints the given int to the streams.
   * 
   * @param x the object to print
   */
    void println(int x);

  /**
   * prints the given long to the streams.
   * 
   * @param x the object to print
   */
    void println(long x);

  /**
   * prints the given float to the streams.
   * 
   * @param x the object to print
   */
    void println(float x);

  /**
   * prints the given double to the streams.
   * 
   * @param x the object to print
   */
    void println(double x);

  /**
   * prints the given bool to the streams.
   * 
   * @param x the object to print
   */
    void println(bool x);

  /**
   * prints the given char to the streams.
   * 
   * @param x the object to print
   */
    void println(char x);

  /**
   * prints the given char array to the streams.
   * 
   * @param x the object to print
   */
    void println(char* x);

  /**
   * prints the given string to the streams.
   * 
   * @param x the object to print
   */
    void println(string x);

  /**
   * prints the given object to the streams (for Throwables we print the stack
   * trace).
   * 
   * @param x the object to print
   */
    void println(Object x);

  /**
   * Writes <code>len</code> bytes from the specified byte array starting at
   * offset <code>off</code> to this stream.  If automatic flushing is
   * enabled then the <code>flush</code> method will be invoked.
   *
   * <p> Note that the bytes will be written as given; to write characters
   * that will be translated according to the platform's default character
   * encoding, use the <code>print(char)</code> or <code>println(char)</code>
   * methods.
   *
   * @param  buf   A byte array
   * @param  off   Offset from which to start taking bytes
   * @param  len   Number of bytes to write
   */
    void write(byte buf[], int off, int len);

  /**
   * Writes the specified byte to this stream.  If the byte is a newline and
   * automatic flushing is enabled then the <code>flush</code> method will be
   * invoked.
   *
   * <p> Note that the byte is written as given; to write a character that
   * will be translated according to the platform's default character
   * encoding, use the <code>print(char)</code> or <code>println(char)</code>
   * methods.
   *
   * @param  b  The byte to be written
   * @see #print(char)
   * @see #println(char)
   */
    void write(int b);

  /**
   * returns only the classname and the number of streams.
   * 
   * @return only the classname and the number of streams
   */
    string toString();
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 5057 $");
  }
};
