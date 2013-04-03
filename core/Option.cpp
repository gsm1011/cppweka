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

/** 
 * Class to store information about an option. <p>
 *
 * Typical usage: <p>
 *
 * <code>Option myOption = new Option("Uses extended mode.", "E", 0, "-E")); </code><p>
 *
 * @author Eibe Frank (eibe@cs.waikato.ac.nz)
 * @version $Revision: 1.7 $
 */
class Option : public RevisionHandler {
private:
    /** What does this option do? */
    string m_Description;

    /** The synopsis. */
    string m_Synopsis;

    /** What's the option's name? */
    string m_Name;

    /** How many arguments does it take? */
    int m_NumArguments;

public:
    Option(string description, string name, 
	   int numArguments, string synopsis) {
  
	m_Description = description;
	m_Name = name;
	m_NumArguments = numArguments;
	m_Synopsis = synopsis;
    }

    Option Option(const Option& other); 

    string description() {
  
	return m_Description;
    }

    string name() { return m_Name; }

    int numArguments() { return m_NumArguments; }

    string synopsis() { return m_Synopsis; }
  
    string getRevision() { return RevisionUtils.extract("$Revision: 1.7 $"); }
};
