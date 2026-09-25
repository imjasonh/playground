/**
 * Entry point. The app is split into focused modules under ./ui plus a
 * controller that wires them together; this file just boots the controller
 * once the DOM is ready. index.html loads it as the page's module script.
 */
import { init } from './controller.js';

if (typeof document !== 'undefined') {
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
}
