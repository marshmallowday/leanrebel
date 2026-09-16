"""Regenerate reviewed source excerpts; this does not renew their semantic review."""
from pathlib import Path
import json, hashlib, sys
r = Path(sys.argv[1])
specs = [
('Protocol/Execution','GameTheory.Protocol.ExecutionProtocol',47,70,'FOUND-MODEL','Legal joint-action FinDist transition and progress are fields. Supply rewards, bounded horizon, finiteness and ReBeL observation model separately.'),
('Protocol/History','GameTheory.Protocol.ExecutionProtocol.historyFintype',73,75,'FOUND-HISTORY','Requires Fintype E.State AND E.IsTreeShaped. Merging histories cannot be discarded just because world states are finite.'),
('Protocol/Information','GameTheory.Protocol.InfoSignals',135,157,'FOUND-INFO','InfoState may compress history. Initial signals and pushInfo do not establish paper AOH equivalence.'),
('Protocol/Information','GameTheory.Protocol.InfoSignals.PerfectRecall',297,301,'FOUND-INFO','Equality of information states must preserve ownPlay; this is a proposition to discharge, not a record default.'),
('Protocol/Information','GameTheory.Protocol.InformationModel',348,360,'FOUND-INFO','menu_adequate quantifies over every realized trace, including terminal states; hidden states cannot change a shared legal menu.'),
('Protocol/Assessment','GameTheory.Protocol.InformationModel.isNash_toGameForm_of_isOneShotOptimalWithin',430,436,'FOUND-NASH','Requires decidable information equality and one-shot optimality at every relevant history within horizon for each player. Not inferred from on-path optimality.'),
('Protocol/BehavioralAssessment','GameTheory.Protocol.InformationModel.bayesBelief',259,266,'PBS-LAW','Requires Fintype information fiber, history antichain and strictly positive information mass; result is a personal posterior, not PBS.'),
('Protocol/BehavioralAssessment','GameTheory.Protocol.InformationModel.BehavioralAssessment.continuationContext',168,173,'PBS-SUBGAME','Requires finite players/decidable player equality. Uses supplied assessment belief and whole-policy unilateral replacement.'),
('Protocol/Strategic','GameTheory.Protocol.InformationModel.toGameForm_mixed_play_toMixed',197,203,'POLICY-AVERAGE','Finite/decidable information states and ActsOnceWhereItMatters; static product pre-draw is not arbitrary per-step mixture.'),
('Protocol/Strategic','GameTheory.Protocol.InformationModel.toGameForm_mixed_play_toBehavioral',208,213,'PBS-EQUIVALENCE','Requires ConstrainsAlike; equality of play distributions alone does not prove preservation of unilateral deviations.'),
('Languages/FOSG','GameTheory.Languages.FOSG.Game',25,30,'FOUND-MODEL','Thin wrapper around ExecutionProtocol and InformationModel; no built-in utility/finite-horizon/PBS theorem.'),
('Analysis/Protocol/CounterfactualReach','GameTheory.Protocol.InformationModel.historyReachProbability_eq_player_mul_counterfactual',492,498,'CFR-REACH','Finite players and decidable equality; counterfactual factor includes chance. This does not make private histories independent.'),
('Analysis/Protocol/CounterfactualRegret','GameTheory.Protocol.InformationModel.counterfactualActionRegret_eq_sub_expect',381,395,'CFR-REGRET','Requires ActsOnceWhereItMatters, finite information fiber, all-nonterminal site and fuel+1; must supply realized continuation payoff.'),
('Analysis/Protocol/CounterfactualRegret','GameTheory.Protocol.InformationModel.counterfactualRegret_pos_iff_bayesGain_pos_of_perfectRecall',787,802,'CFR-REGRET','Perfect recall, antichain, positive mass and finite fiber; zero-reach PBS branches remain a separate obligation.'),
('Analysis/Protocol/CounterfactualRegretMatching','GameTheory.Protocol.InformationModel.counterfactualRegretMatch_sq_infDist_avg_le',162,186,'CFR-MATCH','Pointwise hrealize for every law/environment, uniform norm hbound and bound>=0; finite nonempty action carrier. This is a local matcher, not a whole-game scheduler.'),
('Analysis/Protocol/CounterfactualRootRegret','GameTheory.Protocol.InformationModel.counterfactualRegretMatches_positiveRootGains_le',140,178,'CFR-SCHEDULE','Finite sites, same local process for every deviation, reach in [0,1], hgain upper decomposition and t>0 are supplied. Need a concrete shared play trace and counterfactual realization.'),
('Analysis/Protocol/CounterfactualRootRegret','GameTheory.Protocol.InformationModel.counterfactualRegretMatches_positiveRootGains_tendsto_zero',201,244,'CFR-NASH','In addition to hgain, assumes each local process tends to its orthant via hlocal. Does not construct the ReBeL game-wide process.'),
('Analysis/Minimax','GameTheory.exists_value',39,46,'VAL-LEMMA2','Finite nonempty pure strategies for both players, GameForm(Fin 2), zero-sum utility. Enumerate finite behavioral/pure-plan game and transfer deviations before use.'),
('Analysis/MatrixValue','GameTheory.MatrixGame.abs_value_sub_le_of_entrywise_abs_le',247,248,'SEARCH-ERROR','Finite nonempty row/column sets and uniform entrywise payoff error. Matrix value continuity is not automatically typewise counterfactual oracle safety.'),
('Analysis/ZeroSumLearning','GameTheory.MatrixGame.marginalProfile_isεNash_of_externalRegret_le',295,302,'CFR-NASH','Given one statusQuo joint FinDist and uniform row/column external-regret bounds; epsilon is their sum, not half. Need realization-equivalent behavioral average.'),
('Core/ZeroSum','GameTheory.isNash_iff_isSaddlePoint',124,127,'FOUND-NASH','Two-player mixed GameForm and zero-sum utility; zero-sum assumptions are not implied by arbitrary protocol.'),
('Core/FictitiousPlay','GameTheory.UtilityGame.IsFictitiousPlay',89,93,'VAR-FLOP','Uniform empirical-belief FP recurrence with finite players and decidable equality; not linear optimistic GWFP.'),
('Tests/ReBeLSourceDiagnostics','GameTheory.ReBeL.SourceDiagnostics.not_global_support',56,57,'VAL-THEOREM1','Existing rational diagnostic only. No game embedding or real-domain differentiability theorem is present.')]
items = []
for f, n, a, b, parent, review in specs:
    p = 'GameTheory/' + f + '.lean'
    raw = (r / p).read_bytes()
    segment = '\n'.join(raw.decode().splitlines()[a-1:b]) + '\n'
    items.append({'module':p,'declaration':n,'lines':[a,b],
                  'sha256':hashlib.sha256(raw).hexdigest(),'source_excerpt':segment,
                  'parent':parent,'review':review,'status':'candidate_not_applied'})
out = {'schema':1,'source_commit':'ec152983ce74c6d5c56bf5e16ae6add5e1bab245',
       'scope':'Audited source declarations plus enclosing module assumptions; not an elaborated-type or applicability certificate. Full module hashes pin surrounding variables.',
       'items':items}
(r / 'docs/rebel/inventory/reuse.json').write_text(json.dumps(out, ensure_ascii=False, indent=2)+'\n')
print(len(items), 'reuse entries; recorded review is not re-certified by generation')
