#ifndef PRINTMESSAGE_HPP_
#define PRINTMESSAGE_HPP_

namespace MinisatID{
class idpexception;

namespace Print{
	void printMainStart(int v);
	void printMainEnd(int v);

	void printInitDataStart(int v);
	void printInitDataEnd(int v, double parsetime, bool unsat);

	void printSimpStart(int v);
	void printSimpEnd(int v, bool unsat);

	void printSolveStart(int v);
	void printSolveEnd(int v);

	void printUnsat(int v);

	void printExceptionCaught(const idpexception& e, int v);
	void printUnexpectedError(int v);
}

}

#endif /* PRINTMESSAGE_HPP_ */
