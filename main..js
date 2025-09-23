(function () {
	"use strict";

	// ===================== Utilities =====================
	const FILES = ["a","b","c","d","e","f","g","h"];
	const RANKS = [1,2,3,4,5,6,7,8];
	const inBounds = (x, y) => x >= 0 && x < 8 && y >= 0 && y < 8;
	const algebraic = (x, y) => `${FILES[x]}${RANKS[y]}`;
	const fromAlgebraic = (sq) => [FILES.indexOf(sq[0]), RANKS.indexOf(Number(sq[1]))];

	// ===================== Game State =====================
	const EMPTY = null;
	const WHITE = "w";
	const BLACK = "b";

	const PIECES = {
		w: { K: "\u2654", Q: "\u2655", R: "\u2656", B: "\u2657", N: "\u2658", P: "\u2659" },
		b: { K: "\u265A", Q: "\u265B", R: "\u265C", B: "\u265D", N: "\u265E", P: "\u265F" }
	};
	const PIECE_VALUE = { P: 1, N: 3, B: 3, R: 5, Q: 9, K: 0 };

	/** Board is [y][x] = { type: 'KQRBNP', color: 'w'|'b' } | null */
	let board = Array.from({ length: 8 }, () => Array(8).fill(EMPTY));

	let turn = WHITE;
	let selected = null; // {x,y}
	let legalTargets = []; // [{x,y, capture?:boolean, special?:string}]
	let showLegal = true;

	// Castling rights and en passant target
	let castlingRights = { w: { K: true, Q: true }, b: { K: true, Q: true } };
	let enPassantTarget = null;

	// Overlay control
	let gameOver = false;

	// Captures tracking: pieces captured by white and by black
	let capturedByWhite = [];
	let capturedByBlack = [];

	// Draw rules: position repetition (threefold)
	let positionCounts = new Map(); // key -> count

	function setupInitialPosition() {
		board = Array.from({ length: 8 }, () => Array(8).fill(EMPTY));
		const back = ["R","N","B","Q","K","B","N","R"];
		for (let x = 0; x < 8; x++) {
			board[0][x] = { type: back[x], color: WHITE };
			board[1][x] = { type: "P", color: WHITE };
			board[6][x] = { type: "P", color: BLACK };
			board[7][x] = { type: back[x], color: BLACK };
		}
		turn = WHITE;
		selected = null;
		legalTargets = [];
		castlingRights = { w: { K: true, Q: true }, b: { K: true, Q: true } };
		enPassantTarget = null;
		gameOver = false;
		capturedByWhite = [];
		capturedByBlack = [];
		positionCounts = new Map();
		hideOverlay();
		renderCaptures(); renderScores();
		// record initial position
		incrementPositionCount();
	}

	// ===================== Move Generation =====================
	function getPiece(x, y) { return inBounds(x, y) ? board[y][x] : null; }
	function enemy(color) { return color === WHITE ? BLACK : WHITE; }
	function isEmpty(x, y) { return getPiece(x, y) === EMPTY; }
	function isEnemy(x, y, color) { const p = getPiece(x, y); return p && p.color !== color; }

	function isSquareAttacked(b, x, y, byColor) {
		const pawnDir = byColor === WHITE ? 1 : -1;
		for (const dx of [-1, 1]) { const px = x + dx; const py = y - pawnDir; if (inBounds(px, py)) { const p = b[py][px]; if (p && p.color === byColor && p.type === "P") return true; } }
		const knightDeltas = [[1,2],[2,1],[2,-1],[1,-2],[-1,-2],[-2,-1],[-2,1],[-1,2]];
		for (const [dx, dy] of knightDeltas) { const nx = x + dx, ny = y + dy; if (!inBounds(nx, ny)) continue; const p = b[ny][nx]; if (p && p.color === byColor && p.type === "N") return true; }
		for (let dx = -1; dx <= 1; dx++) { for (let dy = -1; dy <= 1; dy++) { if (dx === 0 && dy === 0) continue; const nx = x + dx, ny = y + dy; if (!inBounds(nx, ny)) continue; const p = b[ny][nx]; if (p && p.color === byColor && p.type === "K") return true; } }
		const diagDirs = [[1,1],[1,-1],[-1,1],[-1,-1]];
		for (const [dx, dy] of diagDirs) { let nx = x + dx, ny = y + dy; while (inBounds(nx, ny)) { const p = b[ny][nx]; if (p) { if (p.color === byColor && (p.type === "B" || p.type === "Q")) return true; break; } nx += dx; ny += dy; } }
		const orthoDirs = [[1,0],[-1,0],[0,1],[0,-1]];
		for (const [dx, dy] of orthoDirs) { let nx = x + dx, ny = y + dy; while (inBounds(nx, ny)) { const p = b[ny][nx]; if (p) { if (p.color === byColor && (p.type === "R" || p.type === "Q")) return true; break; } nx += dx; ny += dy; } }
		return false;
	}

	function generateMovesForSquare(x, y, considerCheck = true) {
		const piece = getPiece(x, y); if (!piece) return [];
		const { type, color } = piece; let moves = [];
		const pushIfEmpty = (nx, ny) => { if (inBounds(nx, ny) && isEmpty(nx, ny)) moves.push({ x: nx, y: ny }); };
		const pushIfCapture = (nx, ny) => { if (inBounds(nx, ny) && isEnemy(nx, ny, color)) moves.push({ x: nx, y: ny, capture: true }); };
		const ray = (dx, dy) => { let nx = x + dx, ny = y + dy; while (inBounds(nx, ny)) { if (isEmpty(nx, ny)) { moves.push({ x: nx, y: ny }); } else { if (isEnemy(nx, ny, color)) moves.push({ x: nx, y: ny, capture: true }); break; } nx += dx; ny += dy; } };
		switch (type) {
			case "P": {
				const dir = color === WHITE ? 1 : -1; const startRank = color === WHITE ? 1 : 6;
				if (isEmpty(x, y + dir)) { moves.push({ x, y: y + dir }); if (y === startRank && isEmpty(x, y + 2 * dir)) { moves.push({ x, y: y + 2 * dir, doublePawn: true }); } }
				pushIfCapture(x - 1, y + dir); pushIfCapture(x + 1, y + dir);
				if (enPassantTarget) {
					if (enPassantTarget.x === x - 1 && enPassantTarget.y === y + dir) moves.push({ x: x - 1, y: y + dir, capture: true, special: "enpassant" });
					if (enPassantTarget.x === x + 1 && enPassantTarget.y === y + dir) moves.push({ x: x + 1, y: y + dir, capture: true, special: "enpassant" });
				}
				break;
			}
			case "N": { const deltas = [[1,2],[2,1],[2,-1],[1,-2],[-1,-2],[-2,-1],[-2,1],[-1,2]]; for (const [dx, dy] of deltas) { const nx = x + dx, ny = y + dy; if (!inBounds(nx, ny)) continue; if (isEmpty(nx, ny) || isEnemy(nx, ny, color)) moves.push({ x: nx, y: ny, capture: !isEmpty(nx, ny) }); } break; }
			case "B": ray(1,1); ray(1,-1); ray(-1,1); ray(-1,-1); break;
			case "R": ray(1,0); ray(-1,0); ray(0,1); ray(0,-1); break;
			case "Q": ray(1,0); ray(-1,0); ray(0,1); ray(0,-1); ray(1,1); ray(1,-1); ray(-1,1); ray(-1,-1); break;
			case "K": {
				for (let dx = -1; dx <= 1; dx++) { for (let dy = -1; dy <= 1; dy++) { if (dx === 0 && dy === 0) continue; const nx = x + dx, ny = y + dy; if (!inBounds(nx, ny)) continue; if (isEmpty(nx, ny) || isEnemy(nx, ny, color)) moves.push({ x: nx, y: ny, capture: !isEmpty(nx, ny) }); } }
				const rights = castlingRights[color === WHITE ? "w" : "b"]; const yHome = color === WHITE ? 0 : 7;
				if (y === yHome && x === 4 && !inCheck(color)) {
					if (rights.K && isEmpty(5, yHome) && isEmpty(6, yHome) && !isSquareAttacked(board, 5, yHome, enemy(color)) && !isSquareAttacked(board, 6, yHome, enemy(color))) { const rook = getPiece(7, yHome); if (rook && rook.type === "R" && rook.color === color) moves.push({ x: 6, y: yHome, special: "castleK" }); }
					if (rights.Q && isEmpty(3, yHome) && isEmpty(2, yHome) && isEmpty(1, yHome) && !isSquareAttacked(board, 3, yHome, enemy(color)) && !isSquareAttacked(board, 2, yHome, enemy(color))) { const rook = getPiece(0, yHome); if (rook && rook.type === "R" && rook.color === color) moves.push({ x: 2, y: yHome, special: "castleQ" }); }
				}
				break;
			}
		}
		if (!considerCheck) return moves; return moves.filter(m => !wouldLeaveKingInCheck(x, y, m));
	}

	function cloneBoard(b) { return b.map(row => row.map(cell => cell ? { ...cell } : cell)); }
	function findKing(b, color) { for (let yy = 0; yy < 8; yy++) { for (let xx = 0; xx < 8; xx++) { const p = b[yy][xx]; if (p && p.type === "K" && p.color === color) return { x: xx, y: yy }; } } return null; }
	function simulateMove(b, fromX, fromY, move) { const nb = cloneBoard(b); const piece = nb[fromY][fromX]; if (!piece) return nb; nb[fromY][fromX] = EMPTY; if (move.special === "enpassant") { nb[move.y][move.x] = piece; const capY = piece.color === WHITE ? move.y - 1 : move.y + 1; nb[capY][move.x] = EMPTY; return nb; } if (move.special === "castleK") { const yHome = piece.color === WHITE ? 0 : 7; nb[yHome][6] = piece; nb[yHome][5] = nb[yHome][7]; nb[yHome][7] = EMPTY; return nb; } if (move.special === "castleQ") { const yHome = piece.color === WHITE ? 0 : 7; nb[yHome][2] = piece; nb[yHome][3] = nb[yHome][0]; nb[yHome][0] = EMPTY; return nb; } nb[move.y][move.x] = piece; return nb; }
	function wouldLeaveKingInCheck(fromX, fromY, move) { const piece = getPiece(fromX, fromY); if (!piece) return true; const nb = simulateMove(board, fromX, fromY, move); const k = findKing(nb, piece.color); if (!k) return true; return isSquareAttacked(nb, k.x, k.y, enemy(piece.color)); }
	function hasAnyLegalMove(color) { for (let y = 0; y < 8; y++) { for (let x = 0; x < 8; x++) { const p = getPiece(x, y); if (!p || p.color !== color) continue; const moves = generateMovesForSquare(x, y, true); if (moves.length > 0) return true; } } return false; }
	function inCheck(color) { const k = findKing(board, color); if (!k) return false; return isSquareAttacked(board, k.x, k.y, enemy(color)); }

	// ===================== Position key for repetition =====================
	function positionKey() {
		// pieces
		let s = "";
		for (let y = 0; y < 8; y++) {
			for (let x = 0; x < 8; x++) {
				const p = board[y][x];
				s += p ? (p.color + p.type + x + y) : ".";
			}
		}
		// side to move
		s += `|${turn}`;
		// castling rights
		const cr = `${castlingRights.w.K?'K':''}${castlingRights.w.Q?'Q':''}${castlingRights.b.K?'k':''}${castlingRights.b.Q?'q':''}` || '-';
		s += `|${cr}`;
		// en passant target only if an actual en passant capture is possible now
		const ep = (enPassantTarget && enPassantCapturePossible(turn)) ? algebraic(enPassantTarget.x, enPassantTarget.y) : '-';
		s += `|${ep}`;
		return s;
	}

	function enPassantCapturePossible(color) {
		if (!enPassantTarget) return false;
		const dir = color === WHITE ? 1 : -1;
		const tx = enPassantTarget.x; const ty = enPassantTarget.y;
		// A pawn of 'color' must be on (tx-1, ty-dir) or (tx+1, ty-dir)
		for (const dx of [-1, 1]) {
			const px = tx + dx; const py = ty - dir;
			if (!inBounds(px, py)) continue;
			const p = board[py][px];
			if (p && p.type === 'P' && p.color === color) {
				// also ensure the captured pawn exists behind target
				const capY = color === WHITE ? ty - 1 : ty + 1;
				const capPawn = inBounds(tx, capY) ? board[capY][tx] : null;
				if (capPawn && capPawn.type === 'P' && capPawn.color !== color) return true;
			}
		}
		return false;
	}

	function incrementPositionCount() {
		const key = positionKey();
		positionCounts.set(key, (positionCounts.get(key) || 0) + 1);
	}

	// ===================== Rendering =====================
	const boardEl = document.getElementById("chessboard");
	const turnEl = document.getElementById("turn-indicator");
	const resetBtn = document.getElementById("reset-btn");
	const showLegalCheckbox = document.getElementById("show-legal");
	const overlayEl = document.getElementById("overlay");
	const resultTextEl = document.getElementById("result-text");
	const playAgainBtn = document.getElementById("play-again");
	const capWhiteEl = document.getElementById("cap-white");
	const capBlackEl = document.getElementById("cap-black");
	const scoreWhiteEl = document.getElementById("score-white");
	const scoreBlackEl = document.getElementById("score-black");

	function renderBoard() {
		boardEl.innerHTML = ""; boardEl.style.pointerEvents = gameOver ? "none" : "auto";
		for (let y = 7; y >= 0; y--) {
			for (let x = 0; x < 8; x++) {
				const isDark = (x + y) % 2 === 1; const sq = document.createElement("div");
				sq.className = `square ${isDark ? "dark" : "light"}`; sq.dataset.x = String(x); sq.dataset.y = String(y);
				const piece = getPiece(x, y);
				if (piece) { const el = document.createElement("div"); el.className = `piece ${piece.color === WHITE ? "white" : "black"}`; el.textContent = PIECES[piece.color][piece.type]; sq.appendChild(el); }
				if (selected && selected.x === x && selected.y === y) sq.classList.add("selected");
				if (showLegal) { for (const m of legalTargets) { if (m.x === x && m.y === y) { if (m.capture) sq.classList.add("highlight-capture"); else sq.classList.add("highlight-move"); } } }
				sq.addEventListener("click", onSquareClick); boardEl.appendChild(sq);
			}
		}
		const msg = `${turn === WHITE ? "白方" : "黑方"}行棋${inCheck(turn) ? "（將軍）" : ""}`; turnEl.textContent = msg;
	}

	function renderCaptures() {
		if (!capWhiteEl || !capBlackEl) return;
		capWhiteEl.innerHTML = ""; capBlackEl.innerHTML = "";
		for (const t of capturedByWhite) { const d = document.createElement("div"); d.className = "cap-piece"; d.textContent = PIECES.b[t]; capWhiteEl.appendChild(d); }
		for (const t of capturedByBlack) { const d = document.createElement("div"); d.className = "cap-piece"; d.textContent = PIECES.w[t]; capBlackEl.appendChild(d); }
	}

	function calculateScoreDiff() {
		const whiteScore = capturedByWhite.reduce((s, t) => s + (PIECE_VALUE[t] || 0), 0);
		const blackScore = capturedByBlack.reduce((s, t) => s + (PIECE_VALUE[t] || 0), 0);
		return { whiteAdv: Math.max(0, whiteScore - blackScore), blackAdv: Math.max(0, blackScore - whiteScore) };
	}

	function renderScores() {
		if (!scoreWhiteEl || !scoreBlackEl) return;
		const { whiteAdv, blackAdv } = calculateScoreDiff();
		scoreWhiteEl.textContent = whiteAdv > 0 ? `+${whiteAdv}` : "";
		scoreBlackEl.textContent = blackAdv > 0 ? `+${blackAdv}` : "";
	}

	function onSquareClick(e) {
		if (gameOver) return; const target = e.currentTarget; const x = Number(target.dataset.x); const y = Number(target.dataset.y); const piece = getPiece(x, y);
		if (selected) { const m = legalTargets.find(m => m.x === x && m.y === y); if (m) { moveSelectedTo(m); postMoveChecks(); return; } }
		if (piece && piece.color === turn) { selected = { x, y }; legalTargets = generateMovesForSquare(x, y, true); } else { selected = null; legalTargets = []; }
		renderBoard();
	}

	function updateCastlingRightsOnMove(piece, fromX, fromY, toX, toY) {
		const sideKey = piece.color === WHITE ? "w" : "b"; const oppKey = piece.color === WHITE ? "b" : "w";
		if (piece.type === "K") { castlingRights[sideKey].K = false; castlingRights[sideKey].Q = false; }
		if (piece.type === "R") { const yHome = piece.color === WHITE ? 0 : 7; if (fromY === yHome && fromX === 0) castlingRights[sideKey].Q = false; if (fromY === yHome && fromX === 7) castlingRights[sideKey].K = false; }
		const captured = getPiece(toX, toY); if (captured && captured.type === "R") { const yHomeOpp = captured.color === WHITE ? 0 : 7; if (toY === yHomeOpp && toX === 0) castlingRights[oppKey].Q = false; if (toY === yHomeOpp && toX === 7) castlingRights[oppKey].K = false; }
	}

	function moveSelectedTo(move) {
		const { x: fromX, y: fromY } = selected; const piece = getPiece(fromX, fromY);
		if (!move.special || move.special.indexOf("castle") === -1) { updateCastlingRightsOnMove(piece, fromX, fromY, move.x, move.y); }
		enPassantTarget = null;
		if (move.special === "enpassant") {
			const capY = piece.color === WHITE ? move.y - 1 : move.y + 1; const captured = getPiece(move.x, capY);
			if (captured) { if (piece.color === WHITE) capturedByWhite.push(captured.type); else capturedByBlack.push(captured.type); }
			board[capY][move.x] = EMPTY; board[move.y][move.x] = piece; board[fromY][fromX] = EMPTY;
		} else if (move.special === "castleK") {
			const yHome = piece.color === WHITE ? 0 : 7; board[yHome][6] = piece; board[fromY][fromX] = EMPTY; board[yHome][5] = board[yHome][7]; board[yHome][7] = EMPTY; const sideKey = piece.color === WHITE ? "w" : "b"; castlingRights[sideKey].K = false; castlingRights[sideKey].Q = false;
		} else if (move.special === "castleQ") {
			const yHome = piece.color === WHITE ? 0 : 7; board[yHome][2] = piece; board[fromY][fromX] = EMPTY; board[yHome][3] = board[yHome][0]; board[yHome][0] = EMPTY; const sideKey = piece.color === WHITE ? "w" : "b"; castlingRights[sideKey].K = false; castlingRights[sideKey].Q = false;
		} else {
			const destPiece = getPiece(move.x, move.y);
			if (destPiece) { if (piece.color === WHITE) capturedByWhite.push(destPiece.type); else capturedByBlack.push(destPiece.type); }
			board[move.y][move.x] = piece; board[fromY][fromX] = EMPTY;
		}
		if (piece.type === "P") { if ((piece.color === WHITE && move.y === 7) || (piece.color === BLACK && move.y === 0)) { piece.type = "Q"; } if (move.doublePawn) { const midY = piece.color === WHITE ? fromY + 1 : fromY - 1; enPassantTarget = { x: move.x, y: midY }; } }
		selected = null; legalTargets = []; turn = enemy(turn);
		// update repetition table after move
		incrementPositionCount();
		renderBoard(); renderCaptures(); renderScores();
	}

	// ===================== Draw helpers =====================
	function isThreefoldRepetition() {
		const key = positionKey();
		return (positionCounts.get(key) || 0) === 3;
	}
	function insufficientMaterial() {
		let bishops = []; let knights = 0; let rooks = 0; let queens = 0; let pawns = 0;
		for (let y = 0; y < 8; y++) {
			for (let x = 0; x < 8; x++) {
				const p = board[y][x]; if (!p) continue;
				if (p.type === 'K') continue;
				if (p.type === 'P') { pawns++; continue; }
				if (p.type === 'N') { knights++; continue; }
				if (p.type === 'R') { rooks++; continue; }
				if (p.type === 'Q') { queens++; continue; }
				if (p.type === 'B') { bishops.push((x + y) % 2); continue; }
			}
		}
		if (pawns > 0 || rooks > 0 || queens > 0) return false;
		if (knights === 0 && bishops.length === 0) return true;
		if (knights === 1 && bishops.length === 0) return true;
		if (knights === 0 && bishops.length === 1) return true;
		if (knights === 0 && bishops.length === 2) { return bishops[0] === bishops[1]; }
		return false;
	}

	function postMoveChecks() {
		const mover = enemy(turn);
		const inChk = inCheck(turn);
		const anyMoves = hasAnyLegalMove(turn);
		if (!anyMoves) {
			if (inChk) { gameOver = true; showOverlay(`${mover === WHITE ? "白方" : "黑方"}將死，${mover === WHITE ? "白方" : "黑方"}獲勝！`); }
			else { gameOver = true; showOverlay("和棋（逼和）"); }
			return;
		}
		if (isThreefoldRepetition()) { gameOver = true; showOverlay("和棋（三次重複局面）"); return; }
		if (insufficientMaterial()) { gameOver = true; showOverlay("和棋（子力不足）"); return; }
	}

	// ===================== Overlay helpers =====================
	function showOverlay(message) { if (!overlayEl) return; resultTextEl.textContent = message; overlayEl.hidden = false; boardEl.style.pointerEvents = "none"; }
	function hideOverlay() { if (!overlayEl) return; overlayEl.hidden = true; boardEl.style.pointerEvents = "auto"; }

	// ===================== Controls =====================
	const doReset = () => { hideOverlay(); setupInitialPosition(); renderBoard(); };
	resetBtn.addEventListener("click", () => { doReset(); });
	showLegalCheckbox.addEventListener("change", () => { showLegal = showLegalCheckbox.checked; renderBoard(); });
	if (playAgainBtn) playAgainBtn.addEventListener("click", () => { doReset(); });
	if (overlayEl) overlayEl.addEventListener("click", (e) => { if (e.target === overlayEl) doReset(); });
	document.addEventListener("keydown", (e) => { if (!overlayEl || overlayEl.hidden) return; if (e.key === "Escape") doReset(); });

	// ===================== Init =====================
	setupInitialPosition();
	renderBoard();
})();

