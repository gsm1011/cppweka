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

void Tee::add(PrintStream p) {
    add(p, false);
  }

void Tee::add(PrintStream p, bool timestamp) {
    add(p, timestamp, "");
  }

void Tee::add(PrintStream p, bool timestamp, string prefix) {
    if (m_Streams.contains(p))
      remove(p);

    // make sure it's not NULL
    if (prefix == NULL)
      prefix = "";

    m_Streams.add(p);
    m_Timestamps.add(new Boolean(timestamp));
    m_Prefixes.add(prefix);
  }

PrintStream Tee::get(int index) {
    if ( (index >= 0) && (index < size()) )
      return (PrintStream) m_Streams.get(index);
    else
      return NULL;
  }

PrintStream Tee::remove(PrintStream p) {
    int         index;

    if (contains(p)) {
      index = m_Streams.indexOf(p);
      m_Timestamps.remove(index);
      m_Prefixes.remove(index);
      return (PrintStream) m_Streams.remove(index);
    }
    else {
      return NULL;
    }
  }

PrintStream Tee::remove(int index) {
    if ( (index >= 0) && (index < size()) ) {
      m_Timestamps.remove(index);
      m_Prefixes.remove(index);
      return (PrintStream) m_Streams.remove(index);
    }
    else {
      return NULL;
    }
  }

bool Tee::contains(PrintStream p) {
    return m_Streams.contains(p);
  }

private:
void Tee::printHeader() {
    for (int i = 0; i < size(); i++) {
      // prefix
      if (!((String) m_Prefixes.get(i)).equals(""))
        ((PrintStream) m_Streams.get(i)).print("[" + m_Prefixes.get(i) + "]\t");
      
      // timestamp
      if (((Boolean) m_Timestamps.get(i)).boolValue())
        ((PrintStream) m_Streams.get(i)).print("[" + new Date() + "]\t");
    }
  }

void Tee::flush() {
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).flush();
  }

void Tee::print(int x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(long x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(float x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(double x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(bool x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(char x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(char* x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(string x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::print(Object x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).print(x);
    flush();
  }

void Tee::println() {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println();
    flush();
  }

void Tee::println(int x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(long x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(float x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(double x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(bool x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(char x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(char * x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(string x) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::println(Object x) {
    string                  line;
    Throwable               t;
    StackTraceElement[]     trace;
    int                     i;

    if (x instanceof Throwable) {
      t     = (Throwable) x;
      trace = t.getStackTrace();
      line  = t.toString() + "\n";
      for (i = 0; i < trace.length; i++)
        line += "\t" + trace[i].toString() + "\n";
      x = line;
    }

    printHeader();
    for (i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).println(x);
    flush();
  }

void Tee::write(byte buf[], int off, int len) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).write(buf, off, len);
    flush();
  }

void Tee::write(int b) {
    printHeader();
    for (int i = 0; i < size(); i++)
      ((PrintStream) m_Streams.get(i)).write(b);
    flush();
  }

string Tee::toString() {
    return this->getClass().getName() + ": " + m_Streams.size();
  }
