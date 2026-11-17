// mute.js — the in-game menu's Mute/Unmute item, shared by the single-player
// and multiplayer controllers, and the "MUTED" badge that keeps the state
// visible on every screen.
import { toggleMuted, isMuted } from './sound.js';

// The item's text: what activating it does.
export function muteItemLabel() {
  return isMuted() ? 'Unmute' : 'Mute';
}

// Toggles the sound and refreshes the badge (`#muted-badge` under root).
export function toggleMute(root) {
  toggleMuted();
  showMutedBadge(root);
}

export function showMutedBadge(root) {
  root.querySelector('#muted-badge')?.classList.toggle('hidden', !isMuted());
}
