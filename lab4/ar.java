import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Cumulative;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.Max;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SmallestMin;
import org.jacop.search.PrintOutListener;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.ui.PrintSchedule;

public class ar {
	public static void main(String args[]) {
		Store store = new Store();
		int dur_add = 1;
		int dur_mul = 2;

		int n = 28;

		int[] last = { 27, 28 };

		int[] add = { 9, 10, 11, 12, 13, 14, 19, 20, 25, 26, 27, 28 };

		int[] mul = { 1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 17, 18, 21, 22, 23, 24 };

		int[][] dependencies = { { 9 }, { 9 }, { 10 }, { 10 }, { 11 }, { 11 }, { 12 }, { 12 }, { 27 }, { 28 }, { 13 },
				{ 14 }, { 16, 17 }, { 15, 18 }, { 19 }, { 19 }, { 20 }, { 20 }, { 22, 23 }, { 21, 24 }, { 25 }, { 25 },
				{ 26 }, { 26 }, { 27 }, { 28 }, {}, {}, };

		int number_add = Integer.parseInt(args[0]);
		int number_mul = Integer.parseInt(args[1]);

		IntVar nbrOfAdds = new IntVar(store, "nbrOfAdds", number_add, number_add);
		IntVar nbrOfMuls = new IntVar(store, "nbrOfMuls", number_mul, number_mul);

		IntVar[] startTimeAdds = new IntVar[add.length];
		IntVar[] startTimeMuls = new IntVar[mul.length];

		// initierar intvars for starttider

		for (int i = 0; i < startTimeAdds.length; i++) {
			startTimeAdds[i] = new IntVar(store, "startTimeAdds" + i, 0,
					(dur_mul > dur_add) ? dur_mul * n : dur_add * n);
		}
		for (int i = 0; i < startTimeMuls.length; i++) {
			startTimeMuls[i] = new IntVar(store, "startTimeMuls" + i, 0,
					(dur_mul > dur_add) ? dur_mul * n : dur_add * n);
		}

		IntVar[] lastVar = new IntVar[last.length];

		// Initierar de sista intVars for de sista operationerna
		int lastIndex = 0;
		for (int i = 0; i < last.length; i++) {
			for (int j = 0; j < add.length; j++) {
				if (add[j] == last[i]) {
					lastIndex = j;
				}
			}

			lastVar[i] = startTimeAdds[lastIndex];
		}

		// statiska intVars for cum och diff constraints. Mangden processorer
		// som varje operation kraver och duration for operationerna

		IntVar[] addDur = new IntVar[add.length];
		IntVar[] mulDur = new IntVar[mul.length];

		IntVar[] resourcesReqAdd = new IntVar[add.length];
		IntVar[] resourcesReqMul = new IntVar[mul.length];

		for (int i = 0; i < addDur.length; i++) {

			addDur[i] = new IntVar(store);
			addDur[i].setDomain(dur_add, dur_add);

		}

		for (int i = 0; i < mulDur.length; i++) {
			mulDur[i] = new IntVar(store);
			mulDur[i].setDomain(dur_mul, dur_mul);

		}

		for (int i = 0; i < resourcesReqAdd.length; i++) {
			resourcesReqAdd[i] = new IntVar(store);
			resourcesReqAdd[i].setDomain(1, 1);

		}
		for (int i = 0; i < resourcesReqMul.length; i++) {
			resourcesReqMul[i] = new IntVar(store);
			resourcesReqMul[i].setDomain(1, 1);

		}

		store.impose(new Cumulative(startTimeAdds, addDur, resourcesReqAdd, nbrOfAdds));
		store.impose(new Cumulative(startTimeMuls, mulDur, resourcesReqMul, nbrOfMuls));

		// Scheman som anvands av Diff2

		IntVar[][] addSchedule = new IntVar[add.length][4];
		IntVar[][] mulSchedule = new IntVar[mul.length][4];

		// Bestammer vilken processor som uytfor vilken operation
		IntVar[] addRecUsed = new IntVar[add.length];

		for (int i = 0; i < addRecUsed.length; i++) {
			addRecUsed[i] = new IntVar(store, "snyggAddNamn"+i,1,number_add);
		}
		IntVar[] mulRecUsed = new IntVar[mul.length];

		for (int i = 0; i < mulRecUsed.length; i++) {
			mulRecUsed[i] = new IntVar(store,"snyggMulNamn"+i,1,number_mul);
		}

		for (int i = 0; i < add.length; i++) {

			addSchedule[i][0] = startTimeAdds[i];// xStart
			addSchedule[i][1] = addRecUsed[i]; // yStart
			addSchedule[i][2] = addDur[i];// xFinish
			addSchedule[i][3] = resourcesReqAdd[i];// yFinish
		}

		for (int i = 0; i < mul.length; i++) {

			mulSchedule[i][0] = startTimeMuls[i];
			mulSchedule[i][1] = mulRecUsed[i];
			mulSchedule[i][2] = mulDur[i];
			mulSchedule[i][3] = resourcesReqMul[i];
		}

		Constraint ctrDiffAdd = new Diff2(addSchedule);
		Constraint ctrDiffMul = new Diff2(mulSchedule);

		store.impose(ctrDiffAdd);
		store.impose(ctrDiffMul);

		int depIndex = -1;
		int thisIndex = -1;
		int duration = -1;
		boolean depInMul = false;
		boolean thisInMul = false;
		// For varje nod i
		for (int i = 0; i < n; i++) {
			//System.out.println("Dependencies length " + dependencies[i].length);
			// For varje nod j som beror pa i
			for (int j = 0; dependencies[i].length != 0 && j < dependencies[i].length; j++) {

				//System.out.println("Starting Search");

				// For varje nod k i add
				for (int k = 0; k < add.length; k++) {
					// Om noden j som beror pa noden i finns i add, spara dess
					// index
					if (add[k] == dependencies[i][j]) {
						depIndex = k;
						depInMul = false;
						//System.out.println("found " + dependencies[i][j] + " on index " + k + " in add when searchin for  depIndex");
					}
				}
				// Om den inte fanns i add, kolla i mul
				if (depIndex == -1) {
					for (int k = 0; k < mul.length; k++) {
						// Om noden j som beror pa noden i finns i mul, spara
						// dess index
						if (mul[k] == dependencies[i][j]) {
							depIndex = k;
							depInMul = true;
							//System.out.println("found " + dependencies[i][j] + " on index " + k + " in mul when searchin for  depIndex");
						}
					}
				}
				// Om inte noden j varken finns i add eller mul ar det nat fel,
				// rappotera
				if (depIndex == -1) {
					System.out.println(dependencies[i][j] + " not found in add or mul.");

				}

				// For varje nod k i add
				for (int k = 0; k < add.length; k++) {
					// om noden i ligger i add, spara index opch satt duration
					// till 1
					if (add[k] == i + 1) {
						duration = dur_add;
						thisIndex = k;
						thisInMul = false;
						//System.out.println("found  " + (i + 1) + " on index " + k + " in add when searchin for  thisIndex");

					}
				}
				if (thisIndex == -1) {
					// om noden i ligger i mul, spara index opch satt duration
					// till 2
					for (int k = 0; k < mul.length; k++) {
						if (mul[k] == i + 1) {
							duration = dur_mul;
							thisIndex = k;
							thisInMul = true;
							//System.out.println("found " + (i + 1) + " on index " + k + " in mul when searchin for  thisIndex");
						}
					}
				}
				// Om inte noden j varken finns i add eller mul ar det nat fel,
				// rappotera
				if (thisIndex == -1) {
					System.out.println(i + 1 + " not found in add or mul.");
				}
				// Noden i:s starttid ar storre an eller lika med noden j:s
				// starttid + duration
				if (!thisInMul && !depInMul) {
					store.impose(new XplusClteqZ(startTimeAdds[thisIndex], duration, startTimeAdds[depIndex]));
				} else if (thisInMul && depInMul) {
					store.impose(new XplusClteqZ(startTimeMuls[thisIndex], duration, startTimeMuls[depIndex]));
				} else if (!thisInMul && depInMul) {
					store.impose(new XplusClteqZ(startTimeAdds[thisIndex], duration, startTimeMuls[depIndex]));
				} else if (thisInMul && !depInMul) {
					store.impose(new XplusClteqZ(startTimeMuls[thisIndex], duration, startTimeAdds[depIndex]));
				}
				// reset variables
				duration = -1;
				thisIndex = -1;
				depIndex = -1;
				depInMul = false;
				thisInMul = false;
			}
		}

		IntVar[] temp = new IntVar[n];
		for (int i = 0; i < startTimeAdds.length; i++) {
			temp[i] = startTimeAdds[i];
		}
		for (int i = 0; i < startTimeMuls.length; i++) {
			temp[startTimeAdds.length+i] = startTimeMuls[i];
		}

		IntVar max = new IntVar(store, "max", 0, n*dur_mul);
		store.impose(new Max(lastVar,max));

		IntVar[] temp2 = new IntVar[n];
		for (int i = 0; i < addRecUsed.length; i++) {
			temp2[i] = addRecUsed[i];
		}
		for (int i = 0; i < mulRecUsed.length; i++) {
			temp2[i+addRecUsed.length] = mulRecUsed[i];
		}

		long t1 = System.currentTimeMillis();
		Search<IntVar> slave = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> selectSlave = new SimpleSelect<IntVar>(temp2, null, new IndomainMin());
		slave.setSelectChoicePoint(selectSlave);

		// sok igenom och skriv ut
		Search<IntVar> search = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> select1 = new SimpleSelect<IntVar>(temp, null, new IndomainMin<IntVar>());
		search.addChildSearch(slave);
		search.setSolutionListener(new PrintOutListener<IntVar>());
		boolean result = search.labeling(store, select1, max);
		long t2 = System.currentTimeMillis();
		if (result) {
			System.out.println("\n*** Yes");
			System.out.println(
					"Solution : " + (dur_add + Integer.max(Integer.parseInt(lastVar[0].toString().split("=")[1].trim()),
							Integer.parseInt(lastVar[1].toString().split("=")[1].trim()))));
			System.out.println("muls: " + java.util.Arrays.toString(startTimeMuls));
			System.out.println("adds: " + java.util.Arrays.toString(startTimeAdds));
			for (int i = 0; i < addRecUsed.length; i++) {
				System.out.println(addRecUsed[i]);
			}
			for (int i = 0; i < mulRecUsed.length; i++) {
				System.out.println(mulRecUsed[i]);
			}
			System.out.println("time: " + (t2-t1));

		} else
			System.out.println("\n*** No");
	}

}
